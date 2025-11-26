import time
import os

# python3 main.py --net example/proof/sample.onnx --spec example/proof/sample.vnnlib --setting_file example/proof/proof_setting.json --device cpu --reasoning_output example/aptp/ --force_split input

def verify(args, onnx_path, vnnlib_path, output_path, timeout):
    # print(f'{result_path=}')
    result_path = f'{output_path}.txt'
    log_path = f'{output_path}.log'
    if os.path.exists(result_path):
        status = open(result_path).read().strip().split(',')[0]
        if status not in ['sat', 'unsat', 'timeout']:
            status = 'error'
        return status
    
    os.chdir(args.verifier_dir)
    
    if os.environ.get('NEURALSAT_SYNTHETIC_BUG_DROP_PROBABILITY') is not None:
        setting_path = os.path.join(args.home_dir, 'verifier/config/neuralsat/settings_bug.json') # attack is disabled for checking synthetic bugs
    else:
        setting_path = os.path.join(args.home_dir, 'verifier/config/neuralsat/settings.json')
    
    assert os.path.exists(setting_path), f"Setting file does not exist: {setting_path=}"
    
    cmd  = f'python3 -W ignore main.py --verbosity=2'
    cmd += f' --net {onnx_path} --spec {vnnlib_path} --timeout {timeout}'
    cmd += f' --result_file {result_path}'
    cmd += f' --setting_file {setting_path}'
    cmd += f' --reasoning_output {output_path}'
    cmd += f' --force_split {args.split_type}'
    cmd += f' --device {args.device}'
    cmd += f' --export_runtime'
    cmd += f' > {log_path} 2>&1'

    tic = time.time()
    # print(f'{cmd=}')
    os.system(cmd)
    toc = time.time()
    
    if os.path.exists(result_path):
        status = open(result_path).read().strip().split(',')[0]
        if status not in ['sat', 'unsat', 'timeout']:
            status = 'error'
    else:
        status = 'error'
        with open(result_path, 'w') as f:
            print(f'{status},{toc - tic}', file=f)
    os.chdir(args.home_dir)
    return status