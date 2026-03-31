import argparse
import os
import pickle

from helper.spec.read_aptp import read_aptp
from helper.tree import BabTree

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
    parser = argparse.ArgumentParser()
    parser.add_argument('--aptp', type=str, required=True,
                        help="path to APTP proof file.")
    parser.add_argument('--output', type=str, required=True,
                        help="output path.")
    args = parser.parse_args()
    objectives, proof = read_aptp(args.aptp)

    # Hidden split
    if len(proof) > 0:
        tree = BinaryTree(objectives, proof)
        tree.export_tree(args.output)
    # Input split
    else:
        tree = BinaryTree(objectives, proof)
        tree.export_tree(args.output)

if __name__ == '__main__':
    main()
