from beartype import beartype
import numpy as np
import torch

from ..network.read_onnx import custom_quirks


class Objective:
    
    "Single objective in CNF"
    
    @beartype
    def __init__(self: 'Objective', prop: tuple[list, tuple[np.ndarray, np.ndarray]]) -> None:
        input_bounds, mat = prop
        self.dtype = torch.get_default_dtype()
        
        bounds = torch.tensor(input_bounds, dtype=self.dtype)
        self.lower_bound = bounds[:, 0]
        self.upper_bound = bounds[:, 1]
        assert torch.all(self.lower_bound <= self.upper_bound)
        self._extract(mat)
        
        
    @beartype
    def _extract(self: 'Objective', mat: tuple[np.ndarray, np.ndarray]) -> None:
        assert len(mat) == 2, print(len(mat))
        prop_mat, prop_rhs = mat
        self.cs = torch.tensor(prop_mat, dtype=self.dtype)
        self.rhs = torch.tensor(prop_rhs, dtype=self.dtype)
        if custom_quirks.get('Softmax', {}).get('skip_last_layer', False):
            assert (self.rhs == 0).all()
    
    
    @beartype
    def get_info(self) -> tuple[torch.Tensor, torch.Tensor]:
        return self.cs, self.rhs
    

class DnfObjectives:
    
    "List of CNF objectives"
    
    @beartype
    def __init__(self, objectives: list[Objective], input_shape: tuple) -> None:
        self.objectives = objectives
        self.input_shape = input_shape
        self._extract()
        self.num_used = 0
        
        
    @beartype
    def __len__(self: 'DnfObjectives') -> int:
        return len(self.lower_bounds[self.num_used:])
    
    
    @beartype
    def pop(self: 'DnfObjectives', batch: int):
        if isinstance(self.cs, torch.Tensor):
            batch = min(batch, len(self))
        else:
            batch = 1
        assert len(self.lower_bounds) == len(self.upper_bounds) == len(self.cs) == len(self.rhs)

        class TMP:
            pass
        objective = TMP()
        
        # indices
        objective.ids = self.ids[self.num_used : self.num_used + batch]
        
        # input bounds
        objective.lower_bounds = self.lower_bounds[self.num_used : self.num_used + batch]
        objective.upper_bounds = self.upper_bounds[self.num_used : self.num_used + batch]
        
        # specs
        objective.cs = self.cs[self.num_used : self.num_used + batch]
        if not isinstance(objective.cs, torch.Tensor):
            objective.cs = torch.cat(objective.cs)[None]
            
        objective.rhs = self.rhs[self.num_used : self.num_used + batch]
        if not isinstance(objective.rhs, torch.Tensor):
            objective.rhs = torch.cat(objective.rhs)[None]
            
        self.num_used += batch
        return objective
        
    
    @beartype
    def _extract(self: 'DnfObjectives') -> None:
        self.cs, self.rhs = [], []
        self.lower_bounds, self.upper_bounds = [], []
        for objective in self.objectives:
            self.lower_bounds.append(objective.lower_bound)
            self.upper_bounds.append(objective.upper_bound)
            c_, rhs_ = objective.get_info()
            self.cs.append(c_)
            self.rhs.append(rhs_)
            
        # input bounds
        self.lower_bounds = torch.stack(self.lower_bounds)
        self.upper_bounds = torch.stack(self.upper_bounds)

        # indices
        magic_number = 3
        self.ids = torch.arange(0, len(self.cs)) + magic_number
        
        assert torch.all(self.lower_bounds <= self.upper_bounds)
            
        # properties
        if all([_.shape[0] == self.cs[0].shape[0] for _ in self.cs]):
            self.cs = torch.stack(self.cs)
        if all([_.shape[0] == self.rhs[0].shape[0] for _ in self.rhs]):
            self.rhs = torch.stack(self.rhs)
            
    @beartype
    def add(self: 'DnfObjectives', objective) -> None:
        self.num_used -= len(objective.cs)
        