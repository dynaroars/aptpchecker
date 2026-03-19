import gurobipy as grb
import multiprocessing
from tqdm import tqdm
import copy
import time
import math
import os

from abstract_network.abstract_network import AbstractNetwork
from helper.data.proof import ProofQueue, ProofReturnStatus

MULTIPROCESS_MODEL = None

ALLOWED_GUROBI_STATUS_CODES = [
    grb.GRB.OPTIMAL, 
    grb.GRB.INFEASIBLE, 
    grb.GRB.USER_OBJ_LIMIT, 
    grb.GRB.TIME_LIMIT,
    grb.GRB.INF_OR_UNBD, # TODO: investigate this
]

UNSAT_GUROBI_STATUS_CODES = [
    grb.GRB.INFEASIBLE,
    grb.GRB.USER_OBJ_LIMIT,
]

def get_model_params(model):
    total_params = sum(p.numel() for p in model.parameters())
    print(f'{total_params = }')
    return total_params

def _proof_worker_impl(candidate):
    can_node, _, can_var_mapping = candidate
    start_solve_time = time.time()
    can_model = MULTIPROCESS_MODEL.copy()
    assert can_model.Params.BestBdStop > 0
    can_model.update()
    
    # add split constraints
    for literal in can_node.history:
        assert literal != 0
        relu_name, pre_relu_name, neuron_idx = can_var_mapping[abs(literal)]
        pre_var = can_model.getVarByName(f"lay{pre_relu_name}_{neuron_idx}")
        relu_var = can_model.getVarByName(f"ReLU{relu_name}_{neuron_idx}")
        print(f'\t- Found: {literal=}, {pre_var=}, {relu_var=}, {pre_var.lb=:.06f}, {pre_var.ub=:.06f}')
        assert pre_var is not None
        # assert relu_var is not None
        if relu_var is None: # var is None if relu is stabilized
            assert pre_var.lb * pre_var.ub >= 0, print('[!] Missing constraints')
            if (literal < 0 and pre_var.lb >= 0) or (literal > 0 and pre_var.ub <= 0):
                print(f'\t\t\t- Unsat: {literal=}, {pre_var.lb=:.06f}, {pre_var.ub=:.06f}')
                return float('inf') # always unsat
        else:
            if literal > 0: # active
                pre_var.lb = 0
                can_model.addConstr(pre_var == relu_var)
            else: # inactive
                pre_var.ub = 0
                relu_var.lb = 0
                relu_var.ub = 0
        # TODO: remove all other relu_var relevant constraints
    can_model.update()
    can_model.optimize()

    print(f'[+] Solved leaf: {can_node = } in {time.time() - start_solve_time} seconds, {can_model.NumVars=}, {can_model.NumConstrs=} {can_model.status=}')
        
    assert can_model.status in ALLOWED_GUROBI_STATUS_CODES, f'[!] Error: {can_model=} {can_model.status=} {can_node.history=}'

    return can_model.status in UNSAT_GUROBI_STATUS_CODES
    
    
def _proof_worker_node(candidate):
    global MULTIPROCESS_MODEL
    is_solved = _proof_worker_impl(candidate)
    return is_solved, candidate[0]
    
class ProofChecker:
    
    def __init__(self, net, input_shape, objective, verbose=False) -> None:
        self.net = net
        self.objective = copy.deepcopy(objective)
        self.input_shape = input_shape
        self.verbose = verbose
        self.device = 'cpu'
        self.abs_net = AbstractNetwork(self.net, self.input_shape, self.device)

    @property
    def var_mapping(self) -> dict:
        if not hasattr(self, '_var_mapping'):
            self._var_mapping = {}
            count = 1
            for node in self.abs_net.split_nodes():
                assert len(node.inputs) == node.output_shape[0] == 1, f'{node.output_shape=} {len(node.inputs)=}'
                for nid in range(math.prod(node.output_shape)):
                    self._var_mapping[count] = (node.name, node.inputs[0].name, nid)
                    count += 1
        return self._var_mapping
    
    def build_core_checker(self, objective, timeout_per_neuron=15.0):
        c_to_use = objective.cs
        tic = time.time()
        self.abs_net.build_solver_module(
            x_L=objective.lower_bounds.view(self.input_shape),
            x_U=objective.upper_bounds.view(self.input_shape),
            C=c_to_use,
            timeout=timeout_per_neuron, 
        )
        print(f'[+] Build coresolver time: {time.time() - tic=}')
        return self.abs_net.solver_model
        
    def set_objective(self, model: grb.Model, objective):
        new_model = model.copy()

        # Only 1 dnf
        assert objective.rhs.shape[0] == self.abs_net.final_node().solver_vars.shape[0] == 1
        for curr_obj, rhs in zip(self.abs_net.final_node().solver_vars[0], objective.rhs[0]):
            new_model.addConstr(new_model.getVarByName(curr_obj.VarName) - rhs <= 0)
        new_model.update()
        return new_model
    
    def prove(self, proof, batch=1, timeout=3600.0, timeout_per_neuron=15.0):
        start_time = time.time()
        global MULTIPROCESS_MODEL
            
        # step 1: build core model without specific objective
        print(f'\n############ Build MILP ############\n')
        core_solver_model = self.build_core_checker(objective=self.objective, timeout_per_neuron=timeout_per_neuron)
        
        # prove tree timeout
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
        
        print(f"[+] Processing: {len(proof)=}")
        current_proof_queue = ProofQueue(proofs=proof)
        MULTIPROCESS_MODEL = shared_solver_model
        
        # step 2: prove nodes
        progress_bar = tqdm(total=len(current_proof_queue), desc=f"Processing proof")
        while len(current_proof_queue):
            if time.time() - start_time > timeout:
                return ProofReturnStatus.TIMEOUT 
            
            nodes = current_proof_queue.get(batch)
            candidates = [(node, current_proof_queue, self.var_mapping) for node in nodes]
            print(f'[+] Proving {len(candidates)=}')
            max_worker = min(len(candidates), os.cpu_count() // 2)
            with multiprocessing.Pool(max_worker) as pool:
                results = pool.map(_proof_worker_node, candidates, chunksize=1)
            # print('Solved nodes:', results, len(current_proof_queue))
            processed = len(current_proof_queue)
            for (is_solved, solved_node) in results:
                if not is_solved: # a leaf cannot be proved
                    return ProofReturnStatus.UNCERTIFIED # unproved
                current_proof_queue.filter(solved_node) # remove solved node from queue
                
            # print(f'\t- Remaining: {len(current_proof_queue)}')
            processed -= len(current_proof_queue)
            progress_bar.update(processed)
            
        MULTIPROCESS_MODEL = None
        
        return ProofReturnStatus.CERTIFIED # proved
        