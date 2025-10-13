import gurobipy as grb
import multiprocessing
import torch.nn as nn
import numpy as np
import torch
import time
import sys
import os


MULTIPROCESS_MODEL = None

def has_relu_var(model):
    names = [v.VarName for v in model.getVars()]
    if not len(names):
        return False
    relus = [v for v in names if v.startswith('aReLU')]
    return len(relus) > 0


def _mip_solver_worker(candidate):
    """ Multiprocess worker for solving MIP models in build_the_model_mip_refine """

    def get_grb_solution(grb_model, reference, bound_type, eps=1e-5):
        refined = False
        if grb_model.status == 9: # Timed out. Get current bound.
            bound = bound_type(grb_model.objbound, reference)
            refined = abs(bound - reference) >= eps
        elif grb_model.status == 2: # Optimally solved.
            bound = grb_model.objbound
            refined = abs(bound - reference) >= eps
        elif grb_model.status == 15: # Found an lower bound >= 0 or upper bound <= 0, so this neuron becomes stable.
            bound = bound_type(1., -1.) * eps
            refined = True
        else:
            bound = reference
        return bound, refined, grb_model.status

    def solve_ub(model, v, out_ub, eps=1e-5):
        model.setObjective(v, grb.GRB.MAXIMIZE)
        model.reset()
        model.setParam('BestBdStop', -eps)  # Terminiate as long as we find a negative upper bound.
        model.optimize()
        vub, refined, status_ub = get_grb_solution(model, out_ub, min, eps=eps)
        return vub, refined, status_ub

    def solve_lb(model, v, out_lb, eps=1e-5):
        model.setObjective(v, grb.GRB.MINIMIZE)
        model.reset()
        model.setParam('BestBdStop', eps)  # Terminiate as long as we find a positive lower bound.
        model.optimize()
        vlb, refined, status_lb = get_grb_solution(model, out_lb, max, eps=eps)
        return vlb, refined, status_lb

    refine_time = time.time()
    model = MULTIPROCESS_MODEL.copy()
    var_name = candidate
    v = model.getVarByName(var_name)
    out_lb, out_ub = v.LB, v.UB
    eps = 1e-5
    v.LB, v.UB = -np.inf, np.inf
    model.update()

    neuron_refined = False
    if abs(out_lb) < abs(out_ub): # lb is tighter, solve lb first.
        vlb, refined, status_lb = solve_lb(model, v, out_lb, eps=eps)
        neuron_refined = neuron_refined or refined
        if vlb <= 0: # Still unstable. Solve ub.
            vub, refined, status_ub = solve_ub(model, v, out_ub, eps=eps)
            neuron_refined = neuron_refined or refined
        else: # lb >= 0, neuron is stable, we skip solving ub.
            vub, status_ub = out_ub, -1
            
    else: # ub is tighter, solve ub first.
        vub, refined, status_ub = solve_ub(model, v, out_ub, eps=eps)
        neuron_refined = neuron_refined or refined
        if vub >= 0: # Still unstable. Solve lb.
            vlb, refined, status_lb = solve_lb(model, v, out_lb, eps=eps)
            neuron_refined = neuron_refined or refined
        else: # ub <= 0, neuron is stable, we skip solving lb.
            vlb, status_lb = out_lb, -1

         
    print(f"Solving MIP for {v.VarName:<10} (timeout={model.Params.TimeLimit}): [{out_lb:.6f}, {out_ub:.6f}]=>[{vlb:.6f}, {vub:.6f}] ({status_lb}, {status_ub}), time: {time.time()-refine_time:.4f}s, #vars: {model.NumVars}, #constrs: {model.NumConstrs}")
    sys.stdout.flush()

    return var_name, vlb, vub, neuron_refined


def _build_solver_input(model, input_lower, input_upper):
    layer_vars = []
    if input_lower.ndim == 4:
        assert input_lower.size(0) == input_upper.size(0) == 1
        input_lower = input_lower.squeeze(0)
        input_upper = input_upper.squeeze(0)
        
    this_layer_shape = input_lower.shape
    for dim, (lb, ub) in enumerate(zip(input_lower.flatten(), input_upper.flatten())):
        v = model.addVar(lb=lb, ub=ub, obj=0, vtype=grb.GRB.CONTINUOUS, name=f'inp_{dim}')
        layer_vars.append(v)
    layer_vars = np.array(layer_vars).reshape(this_layer_shape).tolist()
    model.update()
    return layer_vars, (input_lower, input_upper)


def _build_solver_linear(model, layer, layer_name, layer_bounds, prev_vars, c, refine):
    global MULTIPROCESS_MODEL
    layer_vars = []
    
    # this layer weight
    weight = layer.weight.clone()
    bias = layer.bias.clone()
    W_plus = torch.clamp(weight, min=0.)
    W_minus = torch.clamp(weight, max=0.)
    
    # this layer bounds
    assert torch.all(layer_bounds[0] <= layer_bounds[1])
    upper = W_plus @ layer_bounds[1] + W_minus @ layer_bounds[0] + bias
    lower = W_plus @ layer_bounds[0] + W_minus @ layer_bounds[1] + bias
    assert torch.all(lower <= upper)
    
    # last layer
    if c is not None:
        weight = c.squeeze(0).mm(weight)
        bias = c.squeeze(0).mm(bias.unsqueeze(-1)).view(-1)

    # this layer vars
    for neuron_idx in range(weight.size(0)):
        v = model.addVar(
            lb=lower[neuron_idx].item(), 
            ub=upper[neuron_idx].item(), 
            obj=0, 
            vtype=grb.GRB.CONTINUOUS, 
            name=f'lay{layer_name}_{neuron_idx}'
        )
        lin_expr = grb.LinExpr(weight[neuron_idx, :], prev_vars) + bias[neuron_idx].item()
        model.addConstr(lin_expr == v)
        layer_vars.append(v)
    model.update()

    # stabilization for hidden layers
    if (c is None) and has_relu_var(model) and refine:
        candidates = [v_.VarName for v_ in layer_vars if v_.lb * v_.ub < 0]
        # print(f'{len(candidates) = }')
        if len(candidates):
            MULTIPROCESS_MODEL = model
            max_worker = min(len(candidates), os.cpu_count() // 2)
            with multiprocessing.Pool(max_worker) as pool:
                solver_results = pool.map(_mip_solver_worker, candidates, chunksize=1)
            MULTIPROCESS_MODEL = None
            
            # update bounds        
            for (var_name, var_lb, var_ub, refined) in solver_results:
                if refined:
                    v_ = model.getVarByName(var_name)
                    v_.lb = max(v_.lb, var_lb)
                    v_.ub = min(v_.ub, var_ub)
            model.update()
            
    # new output bounds
    lower = torch.tensor([v.lb for v in layer_vars])
    upper = torch.tensor([v.ub for v in layer_vars])
    assert torch.all(lower <= upper)
    return layer_vars, (lower, upper)


def _build_solver_relu(model, layer, layer_name, prev_vars):
    # output vars
    layer_vars = []
    
    # constant
    zero_var = model.getVarByName('zero')
    
    # prev vars
    vars_array = np.array(prev_vars)
    this_layer_shape = vars_array.shape
    
    # this layer vars
    count_a_vars = 0
    for neuron_idx, pre_var in enumerate(vars_array.reshape(-1)):
        if pre_var.lb >= 0: # active
            v = pre_var
        elif pre_var.ub <= 0: # inactive
            v = zero_var
        else: # unstable
            # post-relu var
            v = model.addVar(ub=pre_var.ub, lb=0, obj=0, vtype=grb.GRB.CONTINUOUS, name=f'ReLU{layer_name}_{neuron_idx}')
            
            # binary indicator
            a = model.addVar(vtype=grb.GRB.BINARY, name=f'aReLU{layer_name}_{neuron_idx}')

            # relu constraints
            model.addConstr(pre_var - pre_var.lb * (1 - a) >= v, name=f'ReLU{layer_name}_{neuron_idx}_a_0')
            model.addConstr(v >= pre_var, name=f'ReLU{layer_name}_{neuron_idx}_a_1')
            model.addConstr(pre_var.ub * a >= v, name=f'ReLU{layer_name}_{neuron_idx}_a_2')
            model.addConstr(v >= 0, name=f'ReLU{layer_name}_{neuron_idx}_a_3')
            
            # log
            count_a_vars += 1
            
        layer_vars.append(v)
    model.update()
        
    print(f'[MILP] Added: unstable={count_a_vars}, stable={len(vars_array.reshape(-1))-count_a_vars}, total={len(vars_array.reshape(-1))} variables')
    
    # new output bounds
    lower = torch.tensor([v.lb for v in layer_vars])
    upper = torch.tensor([v.ub for v in layer_vars])
    
    layer_vars = np.array(layer_vars).reshape(this_layer_shape).tolist()
    lower = lower.view(this_layer_shape)
    upper = upper.view(this_layer_shape)
    assert torch.all(lower <= upper)
    assert torch.all(lower >= 0.)
    
    return layer_vars, (lower, upper)


def _build_solver_flatten(model, layer, layer_name, prev_vars):
    layer_vars = np.array(prev_vars).reshape(-1).tolist()
    lower = torch.tensor([v.lb for v in layer_vars])
    upper = torch.tensor([v.ub for v in layer_vars])
    assert torch.all(lower <= upper)
    return layer_vars, (lower, upper)



def _build_solver_conv2d(model, layer, layer_name, layer_bounds, prev_vars, refine):
    global MULTIPROCESS_MODEL
    layer_vars = []
    # vars
    prev_vars_array = np.array(prev_vars)
    prev_layer_shape = (1,) + prev_vars_array.shape
    assert len(prev_layer_shape) == 4, f'{len(prev_layer_shape)=}'

    # layer weight
    weight = layer.weight.clone().detach().numpy()
    bias = layer.bias.clone().detach().numpy()

    # this layer bounds
    conv_plus = nn.Conv2d(
        layer.in_channels, 
        layer.out_channels, 
        kernel_size=layer.kernel_size, 
        stride= layer.stride, 
        padding=layer.padding)
    conv_minus = nn.Conv2d(
        layer.in_channels, 
        layer.out_channels, 
        kernel_size=layer.kernel_size, 
        stride= layer.stride, 
        padding=layer.padding
    )
    conv_plus._parameters['weight'] = layer.weight.detach().clone().clamp(min=0)
    conv_minus._parameters['weight'] = layer.weight.detach().clone().clamp(max=0)
    conv_plus._parameters['bias'] = layer.bias.detach().clone() / 2.0
    conv_minus._parameters['bias'] = layer.bias.detach().clone() /2.0

    upper = conv_plus(layer_bounds[1]) + conv_minus(layer_bounds[0])
    lower = conv_plus(layer_bounds[0]) + conv_minus(layer_bounds[1])
    assert torch.all(lower <= upper)
    this_layer_shape = (1,) + upper.shape

    # compute row mapping: from current row to input rows
    in_row_idx_mins = np.arange(this_layer_shape[2]) * layer.stride[0] - layer.padding[0]
    in_row_idx_maxs = in_row_idx_mins + weight.shape[2] - 1
    ker_row_mins = np.zeros(this_layer_shape[2], dtype=int)
    ker_row_maxs = np.ones(this_layer_shape[2], dtype=int) * weight.shape[2]
    ker_row_mins[in_row_idx_mins < 0] = -in_row_idx_mins[in_row_idx_mins < 0]
    ker_row_maxs[in_row_idx_maxs >= prev_layer_shape[2]] = ker_row_maxs[in_row_idx_maxs >= prev_layer_shape[2]] - in_row_idx_maxs[in_row_idx_maxs >= prev_layer_shape[2]] + prev_layer_shape[2] - 1
    in_row_idx_mins = np.maximum(in_row_idx_mins, 0)
    in_row_idx_maxs = np.minimum(in_row_idx_maxs, prev_layer_shape[2] - 1)
        
    # compute column mapping: from current column to input columns
    in_col_idx_mins = np.arange(this_layer_shape[3]) * layer.stride[1] - layer.padding[1]
    in_col_idx_maxs = in_col_idx_mins + weight.shape[3] - 1
    ker_col_mins = np.zeros(this_layer_shape[3], dtype=int)
    ker_col_maxs = np.ones(this_layer_shape[3], dtype=int) * weight.shape[3]
    ker_col_mins[in_col_idx_mins < 0] = -in_col_idx_mins[in_col_idx_mins < 0]
    ker_col_maxs[in_col_idx_maxs >= prev_layer_shape[3]] = ker_col_maxs[in_col_idx_maxs >= prev_layer_shape[3]] - in_col_idx_maxs[in_col_idx_maxs >= prev_layer_shape[3]] + prev_layer_shape[3] - 1
    in_col_idx_mins = np.maximum(in_col_idx_mins, 0)
    in_col_idx_maxs = np.minimum(in_col_idx_maxs, prev_layer_shape[3] - 1)
    
    # add vars and constrs
    neuron_idx = 0
    for out_chan_idx in range(this_layer_shape[1]):
        out_chan_vars = []
        for out_row_idx in range(this_layer_shape[2]):
            out_row_vars = []
            # get row index range from precomputed arrays
            ker_row_min, ker_row_max = ker_row_mins[out_row_idx], ker_row_maxs[out_row_idx]
            in_row_idx_min, in_row_idx_max = in_row_idx_mins[out_row_idx], in_row_idx_maxs[out_row_idx]
            for out_col_idx in range(this_layer_shape[3]):
                # get col index range from precomputed arrays
                ker_col_min, ker_col_max = ker_col_mins[out_col_idx], ker_col_maxs[out_col_idx]
                in_col_idx_min, in_col_idx_max = in_col_idx_mins[out_col_idx], in_col_idx_maxs[out_col_idx]
                # init linear expression
                lin_expr = bias[out_chan_idx]
                # init linear constraint LHS implied by the conv operation
                for in_chan_idx in range(weight.shape[1]):
                    coeffs = weight[out_chan_idx, in_chan_idx, ker_row_min:ker_row_max, ker_col_min:ker_col_max].reshape(-1)
                    # print(f'{in_chan_idx=} {weight.shape=}')
                    gvars = prev_vars_array[in_chan_idx, in_row_idx_min:in_row_idx_max+1, in_col_idx_min:in_col_idx_max+1].reshape(-1)
                    # print(f'{coeffs=} {gvars=}')
                    lin_expr += grb.LinExpr(coeffs, gvars)

                # add the output var and constraint
                var = model.addVar(
                    lb=lower[out_chan_idx, out_row_idx, out_col_idx].item(), 
                    ub=upper[out_chan_idx, out_row_idx, out_col_idx].item(), 
                    obj=0, 
                    vtype=grb.GRB.CONTINUOUS, 
                    name=f'lay{layer_name}_{neuron_idx}'
                )
                model.addConstr(lin_expr == var, name=f'lay{layer_name}_{neuron_idx}_eq')
                neuron_idx += 1

                out_row_vars.append(var)
            out_chan_vars.append(out_row_vars)
        layer_vars.append(out_chan_vars)
        
    assert np.array(layer_vars).shape == this_layer_shape[1:]
    model.update()
    
    # stabilization for hidden layers
    if has_relu_var(model) and refine:
        candidates = [v_.VarName for v_ in np.array(layer_vars).reshape(-1) if v_.lb * v_.ub < 0]
        # print(f'{len(candidates) = }')
        if len(candidates):
            MULTIPROCESS_MODEL = model
            max_worker = min(len(candidates), os.cpu_count() // 2)
            with multiprocessing.Pool(max_worker) as pool:
                solver_results = pool.map(_mip_solver_worker, candidates, chunksize=1)
            MULTIPROCESS_MODEL = None
            
            # update bounds        
            for (var_name, var_lb, var_ub, refined) in solver_results:
                if refined:
                    v_ = model.getVarByName(var_name)
                    v_.lb = max(v_.lb, var_lb)
                    v_.ub = min(v_.ub, var_ub)
            model.update()
        
        
    # new output bounds
    lower = torch.tensor([v.lb for v in np.array(layer_vars).reshape(-1)]).view(this_layer_shape)
    upper = torch.tensor([v.ub for v in np.array(layer_vars).reshape(-1)]).view(this_layer_shape)
    assert torch.all(lower <= upper)
    return layer_vars, (lower, upper)

# FIXME: only support feed-forward networks
def build_milp_solver(net, input_lower, input_upper, timeout=15.0, c=None, name='', refine=True, return_bounds=False):
    # abstract domain
    # _, hidden_bounds = Approximator(net)(input_lower[None], input_upper[None])
    
    # init solver
    solver = grb.Model(name)
    solver.setParam('OutputFlag', False)
    solver.setParam('Threads', 1)
    solver.setParam("FeasibilityTol", 1e-5)
    solver.setParam('BestBdStop', 1e-5) # Terminiate as long as we find a positive lower bound.
    solver.setParam('MIPGap', 1e-2)  # Relative gap between lower and upper objective bound 
    solver.setParam('MIPGapAbs', 1e-2)  # Absolute gap between lower and upper objective bound 
    solver.setParam('TimeLimit', timeout) # timeout per neuron
    
    # all vars
    gurobi_vars = []
        
    # constant
    solver.addVar(lb=0, ub=0, obj=0, vtype=grb.GRB.CONTINUOUS, name='zero')

    # input vars
    input_vars, layer_bounds = _build_solver_input(
        model=solver, 
        input_lower=input_lower, 
        input_upper=input_upper,
    )
    gurobi_vars.append(input_vars)
    # print(f'{input_vars = }')
    
    # layer names
    pre_relu_names = []
    relu_names = []
    
    # layer vars
    layers = list(net.children())
    prev_name = None
    for layer_name, layer in enumerate(layers):
        # print(f'\nProcessing {layer = } ({layer_name=})')
        if isinstance(layer,  nn.Linear):
            new_layer_gurobi_vars, new_layer_bounds = _build_solver_linear(
                model=solver, 
                layer=layer,
                layer_name=layer_name,
                layer_bounds=layer_bounds,
                prev_vars=gurobi_vars[-1],
                c=c if layer == layers[-1] else None,
                refine=refine,
            )
            prev_name = layer_name
        elif isinstance(layer, nn.ReLU):
            new_layer_gurobi_vars, new_layer_bounds = _build_solver_relu(
                model=solver, 
                layer=layer,
                layer_name=layer_name,
                prev_vars=gurobi_vars[-1],
            )
            # save layer name
            pre_relu_names.append((prev_name, np.array(new_layer_gurobi_vars).size))
            relu_names.append(layer_name)
        elif isinstance(layer, nn.Flatten) or 'Flatten()' in str(layer):
            new_layer_gurobi_vars, new_layer_bounds = _build_solver_flatten(
                model=solver, 
                layer=layer,
                layer_name=layer_name,
                prev_vars=gurobi_vars[-1],
            )
        elif isinstance(layer,  nn.Conv2d):
            new_layer_gurobi_vars, new_layer_bounds = _build_solver_conv2d(
                model=solver, 
                layer=layer,
                layer_name=layer_name,
                layer_bounds=layer_bounds,
                prev_vars=gurobi_vars[-1],
                refine=refine,
            )
            prev_name = layer_name
        else:
            print(layer, type(layer))
            raise NotImplementedError(layer)
        # print(f'{new_layer_gurobi_vars = }')
        gurobi_vars.append(new_layer_gurobi_vars)
        layer_bounds = (new_layer_bounds[0].clone(), new_layer_bounds[1].clone())
    
    # print('mip lower:', layer_bounds[0])
    # print('mip upper:', layer_bounds[1])
    solver.update()
    if return_bounds:
        return layer_bounds
    return solver, gurobi_vars, pre_relu_names, relu_names

