import gurobipy as grb
import numpy as np
import torch

from .base import AbstractBase

class AbstractAdd(AbstractBase):

    def __init__(self, attr=None, inputs=None, output_index=0, options=None):
        super().__init__(attr, inputs, output_index, options)
        
    def forward(self, x, y):
        # return sum(x, y) wont't broadcast
        return x + y

    def build_solver(self, *v, model, C=None):
        assert len(v) == 2
        if isinstance(v[0], torch.Tensor) and isinstance(v[1], torch.Tensor):
            # constants if both inputs are tensors
            self.solver_vars = self.forward(v[0], v[1])
            return self.solver_vars

        if isinstance(v[0], torch.Tensor):
            v = (v[0].cpu() + torch.zeros(np.array(v[1]).shape), v[1])
        elif isinstance(v[1], torch.Tensor):
            v = (v[0], v[1].cpu() + torch.zeros(np.array(v[0]).shape))
            
        # pre-check
        assert len(v[0]) == 1, f'{len(v[0])=}'
        gvar_array1 = np.array(v[0])
        gvar_array2 = np.array(v[1])
        this_layer_shape = self.output_shape
        assert gvar_array1.shape == gvar_array2.shape == this_layer_shape
        
        # current layer constraints
        new_layer_gurobi_vars = []
        for neuron_idx, (var1, var2) in enumerate(zip(gvar_array1.reshape(-1), gvar_array2.reshape(-1))):
            if isinstance(var1, grb.Var):
                assert var1.lb != -float('inf') and var1.ub != float('inf')
            if isinstance(var2, grb.Var):
                assert var2.lb != -float('inf') and var2.ub != float('inf'), f'{var2=} {var2.lb=} {var2.ub=}'
                
            var = model.addVar(
                lb=-float('inf'), 
                ub=float('inf'), 
                obj=0, 
                vtype=grb.GRB.CONTINUOUS, 
                name=f'lay{self.name}_{neuron_idx}',
            )
            model.addConstr(var == (var1 + var2), name=f'lay{self.name}_{neuron_idx}_eq')
            new_layer_gurobi_vars.append(var)
            
        assert np.array(new_layer_gurobi_vars).shape == np.prod(this_layer_shape[1:])
        self.solver_vars = np.array(new_layer_gurobi_vars).reshape(this_layer_shape)
        model.update()
        return self.solver_vars
    
    
class AbstractSub(AbstractBase):

    def __init__(self, attr=None, inputs=None, output_index=0, options=None):
        super().__init__(attr, inputs, output_index, options)
        
    def forward(self, x, y):
        return x - y


    def build_solver(self, *v, model, C=None):
        assert len(v) == 2
        if isinstance(v[0], torch.Tensor) and isinstance(v[1], torch.Tensor):
            # constants if both inputs are tensors
            self.solver_vars = self.forward(v[0], v[1])
            return self.solver_vars

        if isinstance(v[0], torch.Tensor):
            v = (v[0].cpu() - torch.zeros(np.array(v[1]).shape), v[1])
        elif isinstance(v[1], torch.Tensor):
            v = (v[0], v[1].cpu() - torch.zeros(np.array(v[0]).shape))
            
        # pre-check
        assert len(v[0]) == 1, f'{len(v[0])=}'
        gvar_array1 = np.array(v[0])
        gvar_array2 = np.array(v[1])
        this_layer_shape = self.output_shape
        assert gvar_array1.shape == gvar_array2.shape == this_layer_shape
        
        # current layer constraints
        new_layer_gurobi_vars = []
        for neuron_idx, (var1, var2) in enumerate(zip(gvar_array1.reshape(-1), gvar_array2.reshape(-1))):
            if isinstance(var1, grb.Var):
                assert var1.lb != -float('inf') and var1.ub != float('inf')
            if isinstance(var2, grb.Var):
                assert var2.lb != -float('inf') and var2.ub != float('inf'), f'{var2=} {var2.lb=} {var2.ub=}'
                
            var = model.addVar(
                lb=-float('inf'), 
                ub=float('inf'), 
                obj=0, 
                vtype=grb.GRB.CONTINUOUS, 
                name=f'lay{self.name}_{neuron_idx}',
            )
            model.addConstr(var == (var1 - var2), name=f'lay{self.name}_{neuron_idx}_eq')
            new_layer_gurobi_vars.append(var)
            
        assert np.array(new_layer_gurobi_vars).shape == np.prod(this_layer_shape[1:])
        self.solver_vars = np.array(new_layer_gurobi_vars).reshape(this_layer_shape)
        model.update()
        return self.solver_vars
    
  