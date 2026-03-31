import argparse
import os
import pickle
import torch
import tqdm
import argparse
import json

from helper.spec.read_aptp import read_aptp
from helper.tree import BabTree
from Experiment.utils import get_total_instances, get_benchmark_list

def get_aptp_stat(aptp_file: str):
    cache_file = f"{os.path.splitext(aptp_file)[0]}.pkl"
    if os.path.exists(cache_file):
        with open(cache_file, "rb") as f:
            tree: BabTree = pickle.load(f)
    else:
        objectives, proof = read_aptp(aptp_file)
        print(f"{aptp_file=}", flush=True)
        tree = BabTree(objectives, proof)
        with open(cache_file, "wb") as f:
            pickle.dump(tree, f)

    ans = {
        "depth": tree.depth,
        "width": tree.width,
        "num_nodes": tree.num_nodes
    }
    print(f"{ans=}")
    return ans


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--benchmark_dir", type=str, required=True, help="Root directory for benchmark")
    p.add_argument("--result_dir", type=str, required=True, help="Root directory for result")
    p.add_argument("--verifier", type=str, required=True, choices=["neuralsat", "abcrown", "marabou"])
    p.add_argument("--split_type", type=str, required=True, choices=["input", "hidden"])
    p.add_argument("--output_file", type=str)

    args = p.parse_args()
    torch.set_default_dtype(torch.float64)

    total_instances = get_total_instances(args)
    print(f'{total_instances=}')
    pbar = tqdm.tqdm(total=total_instances)
    
    print(f'[+] Running {args.verifier=} {args.split_type=}')
    
    stats = dict()

    for benchmark in get_benchmark_list(args):
        pbar.set_description(f'{benchmark=}')
        output_dir = os.path.join(args.result_dir, args.verifier, args.split_type, benchmark)
        os.makedirs(output_dir, exist_ok=True)
        # print(f'{output_dir=}')
        
        benchmark_dir = os.path.join(args.benchmark_dir, benchmark)
        instances_file = os.path.join(benchmark_dir, 'instances.csv')
        assert os.path.exists(instances_file), f"Instances file does not exist: {instances_file=}"

        with open(instances_file, 'r') as f:
            instances = f.readlines()
        stat_benchmark = {
            "width": [],
            "depth": [],
            "num_nodes": []
        }

        for instance in instances:
            onnx, vnnlib, _ = instance.strip().split(',')
            onnx_path = os.path.abspath(os.path.join(benchmark_dir, onnx))
            assert os.path.exists(onnx_path), f"ONNX file does not exist: {onnx_path=}"
            vnnlib_path = os.path.abspath(os.path.join(benchmark_dir, vnnlib))
            assert os.path.exists(vnnlib_path), f"VNNLIB file does not exist: {vnnlib_path=}"
            output_path = os.path.abspath(os.path.join(output_dir, f'{os.path.splitext(os.path.basename(onnx))[0]}_{os.path.splitext(os.path.basename(vnnlib))[0]}'))

            result_path = f'{output_path}.txt'

            assert os.path.exists(result_path), f"{result_path} doesn't exist {args.verifier=} {onnx=}, {vnnlib=}"

            status = open(result_path).read().strip().split(',')[0]
            if status not in ['sat', 'unsat', 'timeout']:
                status = 'error'

            if status == "unsat" and os.path.isdir(output_path):
                aptp_files = [os.path.join(output_path, f) for f in os.listdir(output_path)]
                if len(aptp_files) == 0:
                    print("No proof")
                else:
                    for aptp in aptp_files:
                        assert (aptp.endswith("aptp")
                            or aptp.endswith("proof_result")
                            or aptp.endswith("log")
                            or aptp.endswith("pkl"))
                        if not aptp.endswith("aptp"):
                            continue
                        s = get_aptp_stat(aptp_file=aptp)
                        for key, val in s.items():
                            stat_benchmark[key].append(val)

            pbar.update(1)
        stats[benchmark] = stat_benchmark

    assert args.output_file.endswith(".json"), f"{args.output_file} needs to be a JSON file"
    with open(args.output_file, "w") as f:
        json_str = json.dumps(stats)
        f.write(json_str)

if __name__ == "__main__":
    main()

