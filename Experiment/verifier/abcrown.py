import time
import os

def verify(args, onnx_path, vnnlib_path, output_path, timeout):
    # print(f'{result_path=}')
    result_path = f'{output_path}.txt'
    log_path = f'{output_path}.log'
    if os.path.exists(result_path):
        return open(result_path).read().strip().split(',')[0]   
    
    os.chdir(args.verifier_dir)
    
    if args.split_type == 'input':
        setting_path = os.path.join(args.home_dir, 'verifier/config/abcrown/input.yaml')
    elif args.split_type == 'hidden':
        setting_path = os.path.join(args.home_dir, 'verifier/config/abcrown/hidden.yaml')
    
    assert os.path.exists(setting_path), f"Setting file does not exist: {setting_path=}"
    
    cmd  = f'timeout {timeout}s python3 -W ignore abcrown.py'
    cmd += f' --onnx_path {onnx_path} --vnnlib_path {vnnlib_path} --timeout {timeout}'
    cmd += f' --results_file {result_path}'
    cmd += f' --config {setting_path}'
    cmd += f' --reasoning_output {output_path}'
    cmd += f' > {log_path} 2>&1'

    tic = time.time()
    os.system(cmd)
    toc = time.time()
    
    if os.path.exists(result_path):
        status = open(result_path).read().strip().split(',')[0]
    else:
        status = 'error'
        with open(result_path, 'w') as f:
            print(f'{status},{toc - tic}', file=f)
    os.chdir(args.home_dir)
    return status