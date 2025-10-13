import argparse
import time
import os 

from util.network.read_onnx import parse_onnx
from util.spec.read_aptp import read_aptp
from checker.checker import ProofChecker

if __name__ == '__main__':
    START_TIME = time.time()

    # argument
    parser = argparse.ArgumentParser()
    parser.add_argument('--onnx', type=str, required=True,
                        help="load pretrained ONNX model.")
    parser.add_argument('--aptp', type=str, required=True,
                        help="path to APTP proof file.")
    parser.add_argument('--batch', type=int, default=32,
                        help="maximum number of nodes to check in parallel")
    parser.add_argument('--timeout', type=float, default=1000,
                        help="timeout in seconds")
    args = parser.parse_args()   
    
    # extract APTP/ONNX
    objective, proof = read_aptp(args.aptp)
    net, input_shape, _, _ = parse_onnx(args.onnx)
    print(net)
    
    print(f'{objective.lower_bound=}')
    print(f'{objective.upper_bound=}')
    print(f'{objective.cs=}')
    print(f'{objective.rhs=}')
    print(f'{proof=}')
    print(f'Extract ONNX and APTP in {time.time() - START_TIME:.04f} seconds')
    
    proof_checker = ProofChecker(
        net=net, 
        input_shape=input_shape, 
        objective=objective, 
        verbose=False
    ) 
    
    enable_X = bool(int(os.getenv("X", 0)))
    enable_S = bool(int(os.getenv("S", 0)))
    
    status = proof_checker.prove(
        proof=proof, 
        batch=args.batch, 
        expand_factor=2.0 if enable_X else 1.0, 
        timeout=args.timeout,
        refine=enable_S,
    )
    runtime = time.time() - START_TIME
    print(f'{status=}')
    print(f'{runtime=:.04f} seconds')
    