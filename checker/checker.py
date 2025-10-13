import gurobipy as grb
import multiprocessing
from tqdm import tqdm
import copy
import time
import os

from util.data.proof import ProofQueue, ProofReturnStatus
from milp.milp_solver import build_milp_solver

MULTIPROCESS_MODEL = None
RUNNING_BATCH = None

ALLOWED_GUROBI_STATUS_CODES = [
    grb.GRB.OPTIMAL, 
    grb.GRB.INFEASIBLE, 
    grb.GRB.USER_OBJ_LIMIT, 
    grb.GRB.TIME_LIMIT
]

def get_model_params(model):
    total_params = sum(p.numel() for p in model.parameters())
    print(f'{total_params = }')
    return total_params

def _proof_worker_impl(candidate):
    can_node, can_queue, can_var_mapping, _ = candidate
    start_solve_time = time.time()
    can_model = MULTIPROCESS_MODEL.copy()
    assert can_model.ModelSense == grb.GRB.MINIMIZE
    assert can_model.Params.BestBdStop > 0
    can_model.update()
    
    # add split constraints
    for literal in can_node.history:
        assert literal != 0
        relu_name, pre_relu_name, neuron_idx = can_var_mapping[abs(literal)]
        pre_var = can_model.getVarByName(f"lay{pre_relu_name}_{neuron_idx}")
        relu_var = can_model.getVarByName(f"ReLU{relu_name}_{neuron_idx}")
        # print(f'\t- {pre_relu_name=}, {neuron_idx=}, {relu_name=}')
        # print(f'\t- {literal=} {pre_var=}, {relu_var=} {pre_var.lb=} {pre_var.ub=}')
        # print()
        assert pre_var is not None
        if relu_var is None: # var is None if relu is stabilized
            assert pre_var.lb * pre_var.ub >= 0, print('[!] Missing constraints')
            if (literal < 0 and pre_var.lb > 0) or (literal > 0 and pre_var.ub <= 0):
                # always unsat
                return float('inf')
        else:
            if literal > 0: # active
                can_model.addConstr(pre_var == relu_var)
            else: # inactive
                relu_var.lb = 0
                relu_var.ub = 0
        # TODO: remove all other relu_var relevant constraints
    can_model.update()
    can_model.optimize()

    print(f'Solved leaf: {can_node = } in {time.time() - start_solve_time} seconds, {can_model.NumVars=}, {can_model.NumConstrs=}')
        
    assert can_model.status in ALLOWED_GUROBI_STATUS_CODES, print(f'[!] Error: {can_model=} {can_model.status=} {can_node.history=}')
    if can_model.status == grb.GRB.USER_OBJ_LIMIT: # early stop
        return 1e-5
    if can_model.status == grb.GRB.INFEASIBLE: # infeasible
        return float('inf')
    if can_model.status == grb.GRB.TIME_LIMIT: # timeout
        return can_model.ObjBound
    return can_model.objval
    
    
def _proof_worker_impl_with_timeout(candidate, timeout):
    can_node, can_queue, can_var_mapping, _ = candidate
    start_solve_time = time.time()
    # print(f'Solving internal: {timeout=} {can_node = }')
    can_model = MULTIPROCESS_MODEL.copy()
    can_model.setParam('TimeLimit', timeout)
    assert can_model.ModelSense == grb.GRB.MINIMIZE
    assert can_model.Params.BestBdStop > 0
    can_model.update()
    
    # add split constraints
    for literal in can_node.history:
        assert literal != 0
        relu_name, pre_relu_name, neuron_idx = can_var_mapping[abs(literal)]
        pre_var = can_model.getVarByName(f"lay{pre_relu_name}_{neuron_idx}")
        relu_var = can_model.getVarByName(f"ReLU{relu_name}_{neuron_idx}")
        # print(f'\t- {pre_relu_name=}, {neuron_idx=}, {relu_name=}')
        # print(f'\t- {literal=} {pre_var=}, {relu_var=} {pre_var.lb=} {pre_var.ub=}')
        assert pre_var is not None
        if relu_var is None: # var is None if relu is stabilized
            assert pre_var.lb * pre_var.ub >= 0, print('[!] Missing constraints')
            if (literal < 0 and pre_var.lb > 0) or (literal > 0 and pre_var.ub <= 0):
                # always unsat
                return float('inf')
        else:
            if literal > 0: # active
                can_model.addConstr(pre_var == relu_var)
            else: # inactive
                relu_var.lb = 0
                relu_var.ub = 0
        # TODO: remove all other relu_var relevant constraints
    can_model.update()
    can_model.optimize()

    print(f'Solved internal: {timeout=} {can_node = } in {time.time() - start_solve_time} seconds')
        
    assert can_model.status in ALLOWED_GUROBI_STATUS_CODES, print(f'[!] Error: {can_model=} {can_model.status=} {can_node.history=}')
    if can_model.status == grb.GRB.USER_OBJ_LIMIT: # early stop
        return 1e-5
    if can_model.status == grb.GRB.INFEASIBLE: # infeasible
        return float('inf')
    if can_model.status == grb.GRB.TIME_LIMIT: # timeout
        return can_model.ObjBound
    return can_model.objval


def _proof_worker_node(candidate, timeout=None):
    assert RUNNING_BATCH is not None
    node, queue, _, _ = candidate
    if node is None:
        return False
        
    if not len(queue):
        return False
    
    max_filtered_nodes = queue.get_possible_filtered_nodes(node)
    if not max_filtered_nodes:
        return False
    
    if timeout is None:
        obj_val = _proof_worker_impl(candidate)
    else:
        if not len(node):
            return False
        if len(queue) <= RUNNING_BATCH * 4:
            return False
        obj_val = _proof_worker_impl_with_timeout(candidate, timeout=timeout)
        
    is_solved = obj_val > 0
    if is_solved:
        queue.filter(node)
    return is_solved
    


def _proof_worker(candidate):
    global MULTIPROCESS_MODEL
    solved_node = None
    if _proof_worker_node(candidate): # solved
        node, queue, var_mapping, expand_factor = candidate
        solved_node = node
        # while True:
        if expand_factor > 1:
            for _ in range(2): # expand N times
                node = node // expand_factor
                new_candidate = (node, queue, var_mapping, expand_factor)
                if not _proof_worker_node(new_candidate, timeout=60.0):
                    break
                solved_node = node
    return solved_node
                

class ProofChecker:
    
    def __init__(self, net, input_shape, objective, verbose=False) -> None:
        self.net = net
        self.objective = copy.deepcopy(objective)
        self.input_shape = input_shape
        self.verbose = verbose
        self.device = 'cpu'

    @property
    def var_mapping(self) -> dict:
        if not hasattr(self, '_var_mapping'):
            self._var_mapping = {}
            count = 1
            for (pre_act_name, layer_size), act_name in zip(self.pre_relu_names, self.relu_names):
                for nid in range(layer_size):
                    self._var_mapping[count] = (act_name, pre_act_name, nid)
                    count += 1
        return self._var_mapping
    
    def build_core_checker(self, objective, timeout=15.0, refine=False):
        input_lower = objective.lower_bound.view(*self.input_shape[1:])
        input_upper = objective.upper_bound.view(*self.input_shape[1:])
        c_to_use = objective.cs[None]
        assert c_to_use.shape[1] == 1, f'Unsupported shape {c_to_use.shape=}'
        # c_to_use = c_to_use.transpose(0, 1)

        tic = time.time()
        # print(f'{input_lower.shape=}')
        # print(f'{c_to_use.shape=}')
        solver, solver_vars, self.pre_relu_names, self.relu_names = build_milp_solver(
            net=self.net,
            input_lower=input_lower,
            input_upper=input_upper,
            c=c_to_use,
            timeout=timeout,
            name='APTPchecker',
            refine=refine,
        )    
        build_solver_time = time.time() - tic
        print(f'{build_solver_time=}')
        assert len(objective.cs) == len(solver_vars[-1]) == 1
        self.objective_var_name = solver_vars[-1][0].varName
        return solver
        
    def set_objective(self, model, objective):
        new_model = model.copy()
        rhs_to_use = objective.rhs[0]
        # print(f'{rhs_to_use.shape=}')
        # print(f'{self.objective_var_name=}')
        # setup objective
        objective_var = new_model.getVarByName(self.objective_var_name) - rhs_to_use
        new_model.setObjective(objective_var, grb.GRB.MINIMIZE)
        new_model.update()
        return new_model
    
    def prove(self, proof, batch=1, expand_factor=2.0, timeout=3600.0, timeout_per_neuron=15.0, refine=False):
        start_time = time.time()
        global MULTIPROCESS_MODEL, RUNNING_BATCH
        RUNNING_BATCH = batch
            
        # step 1: build core model without specific objective
        print(f'\n############ Build MILP ############\n')
        core_solver_model = self.build_core_checker(
            objective=self.objective, 
            timeout=timeout_per_neuron, 
            refine=refine,
        )
        core_solver_model.setParam('TimeLimit', timeout)
        core_solver_model.setParam('OutputFlag', self.verbose)
        core_solver_model.update()
        print(f'{core_solver_model=}')
        get_model_params(self.net)
        # set specific objective
        shared_solver_model = self.set_objective(core_solver_model, self.objective)
        
        print(f'\n############ Check Proof ############\n')
        # check timeout
        if time.time() - start_time > timeout:
            return ProofReturnStatus.TIMEOUT 
        
        print(f"Processing: {len(proof)=} {expand_factor=} {refine=}")
        current_proof_queue = ProofQueue(proofs=proof)
        MULTIPROCESS_MODEL = shared_solver_model
        
        # step 2: prove nodes
        progress_bar = tqdm(total=len(current_proof_queue), desc=f"Processing proof")
        while len(current_proof_queue):
            if time.time() - start_time > timeout:
                return ProofReturnStatus.TIMEOUT 
            
            nodes = current_proof_queue.get(batch)
            candidates = [(node, current_proof_queue, self.var_mapping, expand_factor) for node in nodes]
            print(f'Proving {len(candidates)=}')
            max_worker = min(len(candidates), os.cpu_count() // 2)
            with multiprocessing.Pool(max_worker) as pool:
                results = pool.map(_proof_worker, candidates, chunksize=1)
            # print('Solved nodes:', results, len(current_proof_queue))
            processed = len(current_proof_queue)
            for solved_node in results:
                if solved_node is not None:
                    current_proof_queue.filter(solved_node)
                else:
                    # a leaf cannot be proved
                    return ProofReturnStatus.UNCERTIFIED # unproved
                
            # print(f'\t- Remaining: {len(current_proof_queue)}')
            processed -= len(current_proof_queue)
            progress_bar.update(processed)
            
        MULTIPROCESS_MODEL = None
        
        return ProofReturnStatus.CERTIFIED # proved
        