import argparse

from helper.spec.read_aptp import read_aptp
from helper.binary_tree import BinaryTree

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
