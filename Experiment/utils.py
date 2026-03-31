from torch.utils.data import DataLoader
from typing import Any, Dict
import torch.nn as nn
import numpy as np
import random
import torch
import tqdm
import os

BENCHMARK_CONFIG = {
    'input': [
        'acasxu',
        # 'cersyve',
        'cora',
        'safenlp',
        'sat_relu',
        'tllverifybench'
    ],
    'hidden': [
        'acasxu',
        'cora',
        'tllverifybench',
        'fnn_small',
        'fnn_medium',
        'cnn_small',
        'cnn_medium',
        'sat_relu',
        'safenlp',
        'malbeware',
    ]
}

def recursive_walk(rootdir):
    for r, dirs, files in os.walk(rootdir):
        for f in files:
            yield os.path.join(r, f)
            
            
def set_seed(seed: int = 42):
    random.seed(seed)
    np.random.seed(seed)
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)

def get_device() -> torch.device:
    return torch.device("cuda" if torch.cuda.is_available() else "cpu")

def get_model_parameters(model: torch.nn.Module) -> int:
    return sum(p.numel() for p in model.parameters() if p.requires_grad)

def save_checkpoint(path: str, state: Dict[str, Any]):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    torch.save(state, path)

def load_checkpoint(path: str) -> Dict[str, Any]:
    return torch.load(path, map_location="cpu")

def evaluate_model(model: nn.Module, test_loader: DataLoader, device: torch.device) -> float:
    """Evaluate the model on the test set and return accuracy."""
    model.eval()
    correct = 0
    total = 0
    with torch.no_grad():
        for x, y in test_loader:
            x = x.to(device)
            y = y.to(device)
            logits = model(x)
            preds = logits.argmax(dim=1)
            correct += (preds == y).sum().item()
            total += y.numel()
    test_acc = correct / max(total, 1)
    return test_acc

def get_benchmark_list(args) -> list:
    return BENCHMARK_CONFIG[args.split_type]

def get_total_instances(args):
    count = 0
    benchmarks = get_benchmark_list(args)
    print(f'[+] Extracting {args.split_type=}: {benchmarks=}')
    for benchmark_name in get_benchmark_list(args):
        benchmark_dir = os.path.join(args.benchmark_dir, benchmark_name)
        assert os.path.exists(benchmark_dir), f'{benchmark_dir=} does not exist'
        for file in recursive_walk(benchmark_dir):
            if file.endswith('instances.csv'):
                # print(f'{file=}')
                count += len(open(file).readlines())
    return count

def create_vnnlib_str(data_lb: torch.Tensor, data_ub: torch.Tensor, prediction: torch.Tensor, max_specs: int = 1):
    # input bounds
    x_lb = data_lb.flatten()
    x_ub = data_ub.flatten()
    
    # outputs
    n_class = prediction.numel()
    y = prediction.argmax(-1).item()
    
    base_str = f"; Specification for class {int(y)}\n"
    base_str += f"\n; Definition of input variables\n"
    for i in range(len(x_ub)):
        base_str += f"(declare-const X_{i} Real)\n"

    base_str += f"\n; Definition of output variables\n"
    for i in range(n_class):
        base_str += f"(declare-const Y_{i} Real)\n"

    base_str += f"\n; Definition of input constraints\n"
    for i in range(len(x_ub)):
        base_str += f"(assert (<= X_{i} {x_ub[i]:.8f}))\n"
        base_str += f"(assert (>= X_{i} {x_lb[i]:.8f}))\n\n"

    base_str += f"\n; Definition of output constraints\n"
    specs = []
    for i in range(n_class):
        if i == y:
            continue
        spec_i = base_str
        spec_i += f"(assert (or\n"
        spec_i += f"\t(and (>= Y_{i} Y_{y}))\n"
        spec_i += f"))\n"
        specs.append(spec_i)
    return specs[:max_specs]
        