import torch
import tqdm
import os
import time

from utils import get_total_instances, get_benchmark_list
from verifier import neuralsat, abcrown, marabou
from argument import parse_args

APTP_TIMEOUT = 1000

def run_aptp(onnx_path, aptp_path, result_file, log_file, timeout=1000):
    if os.path.exists(result_file):
        status, runtime = open(result_file).read().strip().split(',')

        # Rerun the error proof that don't get timeout
        if float(runtime) >= timeout - 10:
            return status

    cmd  = f'timeout {timeout}s python3 ../main.py'
    cmd += f' --onnx {onnx_path}'
    cmd += f' --aptp {aptp_path}'
    cmd += f' --result_file {result_file} > {log_file} 2>&1'
    tic = time.time()
    os.system(cmd)
    toc = time.time()

    if os.path.exists(result_file):
        status = open(result_file).read().strip().split(',')[0]
    else:
        runtime = toc - tic
        if runtime >= timeout:
            status = 'timeout'
        else:
            status = 'error'
        with open(result_file, 'w') as f:
            print(f'{status},{runtime}', file=f)
    assert status in ['unknown', 'timeout', 'certified', 'uncertified', 'error']
    return status

def main():
    
    torch.set_default_dtype(torch.float64)
    args = parse_args()
    
    if args.verifier == "neuralsat":
        verify_func = neuralsat.verify
    elif args.verifier == "abcrown":
        verify_func = abcrown.verify
    elif args.verifier == "marabou":
        verify_func = marabou.verify
    else:
        raise ValueError(f"Invalid verifier: {args.verifier=}")
    
    total_instances = get_total_instances(args)
    print(f'{total_instances=}')
    pbar = tqdm.tqdm(total=total_instances)
    
    print(f'[+] Running {args.verifier=} {args.split_type=}')
    
    stats = {
        'sat': 0,
        'unsat': 0,
        'timeout': 0,
        'error': 0,
    }

    stats_proof = {
        'certified': 0,
        'not_certified': 0
    }

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
        
        for instance in instances:
            onnx, vnnlib, _ = instance.strip().split(',')
            onnx_path = os.path.abspath(os.path.join(benchmark_dir, onnx))
            assert os.path.exists(onnx_path), f"ONNX file does not exist: {onnx_path=}"
            vnnlib_path = os.path.abspath(os.path.join(benchmark_dir, vnnlib))
            assert os.path.exists(vnnlib_path), f"VNNLIB file does not exist: {vnnlib_path=}"
            output_path = os.path.abspath(os.path.join(output_dir, f'{os.path.splitext(os.path.basename(onnx))[0]}_{os.path.splitext(os.path.basename(vnnlib))[0]}'))
            # print(f'{onnx_path=}')
            # print(f'{vnnlib_path=}')
            # print(f'{output_path=}')
            status = verify_func(args, onnx_path, vnnlib_path, output_path, args.timeout)

            if status == "unsat" and os.path.isdir(output_path):
                certified = True
                aptp_files = [os.path.join(output_path, f) for f in os.listdir(output_path)]
                if len(aptp_files) == 0:
                    print("No proof")
                else:
                    for aptp in aptp_files:
                        assert aptp.endswith("aptp") or aptp.endswith("proof_result")
                        if aptp.endswith("proof_result"):
                            continue

                        res_file = aptp.split(".aptp")[0] + ".proof_result"
                        log_file = aptp.split(".aptp")[0] + ".log"
                        proof_status = run_aptp(
                            onnx_path=onnx_path, 
                            aptp_path=aptp,
                            result_file=res_file,
                            log_file=log_file,
                            timeout=APTP_TIMEOUT
                        )
                        if proof_status != "certified":
                            certified = False
                            break

                proof_result = output_path + ".proof_result"
                if certified:
                    stats_proof['certified'] += 1
                    with open(proof_result, 'w') as f:
                        print(f'certified', file=f)
                else:
                    stats_proof['not_certified'] += 1
                    with open(proof_result, 'w') as f:
                        print(f'uncertified', file=f)

            stats[status] += 1
            pbar.update(1)
            pbar.set_postfix(**stats)
            # exit()
        
        # print()
        print(stats_proof)

if __name__ == "__main__":
    main()
