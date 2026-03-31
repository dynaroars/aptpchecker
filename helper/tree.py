import graphviz
import torch
import time

CYCLE_LOG = 1800

class Node:
    def __init__(self, val, children=None):
        # Hidden split
        self.val = val # what to display
        self.children: list[Node] = children if children is not None else []

        # Input split
        self.lower_bound = None
        self.upper_bound = None
        self.split_index = None

    def set_bounds(self, lower_bound, upper_bound):
        self.lower_bound = lower_bound
        self.upper_bound = upper_bound

    def set_split_index(self, split_index):
        self.split_index = split_index

    def has_child(self, given_value):
        for n in self.children:
            if n.val == given_value:
                return True
        return False

    def find_child(self, given_value):
        for id, n in enumerate(self.children):
            if n.val == given_value:
                return id
        return -1

    def __lt__(self, other):
        return self.val < other.val

    def __repr__(self):
        return f"Node {self.lower_bound=} {self.upper_bound=}"

    def print(self):
        print(f"{self.lower_bound=}")
        print(f"{self.upper_bound=}")

def sort_nodes(nodes: list[Node], split_index):
    return sorted(nodes, key=lambda x: x.lower_bound[split_index].item())


def combine(nodes: list[Node], split_index):
    assert len(nodes) > 0
    if len(nodes) == 1:
        return nodes[0]
    nodes = sort_nodes(nodes, split_index=split_index)
    lower = nodes[0].lower_bound
    upper = nodes[-1].upper_bound

    new_node = Node(f"X_{split_index}\n({lower[split_index].item()}, {upper[split_index].item()})", children=nodes)
    new_node.set_bounds(lower, upper)
    new_node.set_split_index(split_index=split_index)

    prev = nodes[0]
    for node in nodes:
        node.val = f"X_{split_index}\n({node.lower_bound[split_index].item()}, {node.upper_bound[split_index].item()})"
        if node == prev:
            continue
        assert torch.all(torch.isclose(prev.upper_bound[split_index], node.lower_bound[split_index], 1e-5, 1e-5)), \
            f"{prev=} {node=} at {split_index=}"
        assert get_split_index(node, prev) == split_index
        prev = node

    return new_node


def get_split_index(a: Node, b: Node):
    match_lower = (~torch.isclose(a.lower_bound, b.lower_bound, 1e-5, 1e-5)).nonzero()
    match_upper = (~torch.isclose(a.upper_bound, b.upper_bound, 1e-5, 1e-5)).nonzero()

    num_match_lower = match_lower.numel()
    num_match_upper = match_upper.numel()
    if num_match_lower == num_match_upper == 1:
        return match_lower.item()
    return -1

def is_consecutive(node1: Node, node2: Node):
    split_index = get_split_index(node1, node2)
    if split_index == -1:
        return False
    node1, node2 = sort_nodes([node1, node2], split_index=split_index)
    return torch.all(torch.isclose(node1.upper_bound[split_index], node2.lower_bound[split_index], 1e-5, 1e-5))


class Group:
    def __init__(self):
        self.split_index = None
        self.nodes: list[Node] = []

    def set_split_index(self, split_index):
        if self.split_index == None:
            self.split_index = split_index
        else:
            assert self.split_index == split_index, f"{self.splits[-1].lower_bound}"

    def add(self, node):
        self.nodes.append(node)

    def combine_node(self) -> list[Node]:
        nodes = self.nodes
        res: list[Node] = []
        if len(nodes) == 1:
            return [nodes[0]]

        assert self.split_index != None, f"{nodes} do not None split index"
        nodes = sort_nodes(nodes, self.split_index)

        # Modify this
        assert len(nodes) > 0
        possible_matches: list[Node] = [nodes[0]]
        for i in range(1, len(nodes)):
            curr = nodes[i]
            prev = possible_matches[-1]
            # They can be combined
            if torch.all(curr.lower_bound[self.split_index] == prev.upper_bound[self.split_index]):
                possible_matches.append(curr)

            else:
                new_node = combine(possible_matches, self.split_index)
                res.append(new_node)
                possible_matches = [curr]

        new_node = combine(possible_matches, self.split_index)
        res.append(new_node)

        return res

    def __len__(self):
        return len(self.nodes)

    def print(self, s):
        print(f"Splits: {self.split_index=}")
        for i, split in enumerate(s):
            print(f"Input {i}: {split.lower_bound=}")
            print(f"Input {i}: {split.upper_bound=}\n")
        print()

    def print_all(self):
        self.print(self.splits)

class BabTree:
    def __init__(self, objectives, proof_tree):
        self.start_time = time.time()
        self.last_log = time.time()
        self.root = Node("root") # root
        self.objectives = objectives
        self.proof_tree = proof_tree
        if len(proof_tree) > 0:
            self.build_hidden()
        else:
            self.build_input()

    @property
    def num_nodes(self):
        def dfs(node: Node):
            if not node:
                return 0
            ans = 0
            for n in node.children:
                ans += dfs(n)

            return ans + 1

        return dfs(self.root)

    @property
    def width(self):
        max_width = 0
        return max_width

    @property
    def depth(self):
        def dfs(node: Node):
            if not node:
                return 0
            ans = 0
            for n in node.children:
                ans = max(ans, dfs(n))
            return ans + 1

        return dfs(self.root)

    # Old
    # def process(self, nodes):
    #     initial_len = len(nodes)
    #     print(f"Processing {initial_len} nodes")
    #     print(f"{nodes=}")
    #     groups = []
    #     # Find two good consecutive
    #     good = [None, None]
    #     for i in range(initial_len):
    #         for j in range(i + 1, initial_len):
    #             if is_consecutive(nodes[i], nodes[j]):
    #                 good = [i, j]
    #                 break
    #         if good[0] != None:
    #             break
    #     assert good[0] != None

    #     while good[0] != None:
    #         good_group = Group()
    #         good_group.set_split_index(get_split_index(nodes[i], nodes[j]))
    #         good_group.add(nodes[i])
    #         good_group.add(nodes[j])
    #         nodes[i] = None
    #         nodes[j] = None

    #         # If there are more nodes belong to the good group
    #         for i, curr in enumerate(nodes):
    #             if curr == None:
    #                 continue
    #             for n in good_group.nodes:
    #                 if is_consecutive(curr, n) and get_split_index(curr, n) == good_group.split_index:
    #                     good_group.add(curr)
    #                     nodes[i] = None
    #                     break

    #         groups.append(good_group)
    #         good = [None, None]
    #         for i in range(initial_len):
    #             if nodes[i] == None:
    #                 continue
    #             for j in range(i + 1, initial_len):
    #                 if nodes[j] == None:
    #                     continue
    #                 if is_consecutive(nodes[i], nodes[j]):
    #                     good = [i, j]
    #                     break
    #             if good[0] != None:
    #                 break

    #     # Construct groups
    #     # groups = [good_group]

    #     for i, node1 in enumerate(nodes):
    #         # Already processed
    #         if not node1:
    #             continue
    #         curr_group = Group()
    #         curr_group.add(node1)

    #         for j in range(i + 1, len(nodes)):
    #             node2 = nodes[j]

    #             # Already processed
    #             if not node2:
    #                 continue

    #             split_index = get_split_index(node1, node2)

    #             # They cannot combine
    #             if split_index == -1:
    #                 continue
    #             if curr_group.split_index == None:
    #                 curr_group.split_index = split_index
    #                 curr_group.add(node2)
    #                 nodes[j] = None
    #             else:
    #                 if curr_group.split_index != split_index:
    #                     continue
    #                 curr_group.split_index = split_index
    #                 curr_group.add(node2)
    #                 nodes[j] = None

    #         groups.append(curr_group)

    #     new_nodes = []
    #     for group in groups:
    #         print(f"Before: {len(group.nodes)=}\nBefore: {group.nodes=}")
    #         a = group.combine_node()
    #         print(f"After: {len(a)=}\nAfter: {a=}")
    #         new_nodes.extend(a)
    #     assert initial_len > len(new_nodes), f"There is no decrease in number of nodes {initial_len=} {len(new_nodes)=}"
    #     if len(new_nodes) == 1:
    #         return new_nodes[0]
    #     return self.process(new_nodes)

    """
    backtracking
    """
    def process(self, given_nodes: list[Node]):
        curr = time.time()
        runtime = curr - self.start_time
        since_last_log = curr - self.last_log
        if since_last_log > CYCLE_LOG:
            self.last_log = curr
            print(f"Log check at {time.ctime()} {runtime=}", flush=True)
        initial_len = len(given_nodes)
        # print(f"Processing {initial_len} nodes")
        if initial_len == 1:
            return given_nodes[0]

        num_input = given_nodes[0].lower_bound.numel()
        # print(f"{num_input=}")
        # print(f"{given_nodes=}")

        for pick_index in range(num_input):
            nodes = [n for n in given_nodes]
            groups = []
            for i, node1 in enumerate(nodes):
                # Already processed
                if node1 == None:
                    continue
                curr_group = Group()
                curr_group.set_split_index(pick_index)
                curr_group.add(node1)

                for j in range(i + 1, len(nodes)):
                    node2 = nodes[j]
                    if node2 == None:
                        continue

                    split_index = get_split_index(node1, node2)
                    if split_index == pick_index:
                        curr_group.add(node2)
                        nodes[j] = None

                if len(curr_group) == 1:
                    del curr_group
                else:
                    nodes[i] = None # belongs to some group
                    groups.append(curr_group)

            new_nodes = [n for n in nodes if n != None]
            for group in groups:
                # print(f"Before: {len(group.nodes)=}\nBefore: {group.nodes=}")
                a = group.combine_node()
                # print(f"After: {len(a)=}\nAfter: {a=}")
                new_nodes.extend(a)
            if len(new_nodes) < initial_len:
                # print(f"{new_nodes=}")
                res = self.process(new_nodes)
                if res != None:
                    return res

        # assert initial_len > len(new_nodes), f"There is no decrease in number of nodes {initial_len=} {len(new_nodes)=}"
        # assert initial_len > len(new_nodes), "Can't"
        return None


    def build_input(self):
        nodes = []
        for ob in self.objectives.objectives:
            new_node = Node("")
            new_node.lower_bound = ob.lower_bound
            new_node.upper_bound = ob.upper_bound
            nodes.append(new_node)

        # self.root = self.process(nodes)
        self.root = self.process(nodes)
        assert self.root != None, "This proof doesn't work"

    @property
    def num_hidden_proof(self):
        count = dict()
        for proof_step in self.proof_tree:
            for n in proof_step:
                count.setdefault(abs(n), 0)
                count[abs(n)] += 1
        return count

    def build_hidden(self):
        n = len(self.proof_tree)
        for i, proof_step in enumerate(self.proof_tree):
            # if i % 10 == 0:
            #     print(f"Processing {i}/{n} steps")
            proof_step = sorted(proof_step, key=lambda x: self.num_hidden_proof[abs(x)], reverse=True)
            self.process_hidden_list(proof_step)

    def process_hidden_list(self, neurons):
        curr: Node = self.root

        # For hidden split, each node should have 0 or 2 children nodes
        for neuron in neurons:
            if not curr.has_child(neuron):
                curr.children.append(Node(neuron))
                curr.children.sort()

            curr = curr.children[curr.find_child(neuron)]

    def gen_dot(self):
        lines = ["digraph BinaryTree {", "node [shape=circle];"]
        # lines = [
        #     "digraph BinaryTree {",
        #     "node [shape=circle, fixedsize=true, width=1.4, height=1.4];"
        # ]
        def traverse(node: Node):
            if node is None:
                return

            # Use id(node) to uniquely identify nodes
            node_id = id(node)
            lines.append(f'{node_id} [label="{node.val}"];')

            for child in node.children:
                child_id = id(child)
                lines.append(f"{node_id} -> {child_id};")
                traverse(child)

        traverse(self.root)
        lines.append("}")
        return "\n".join(lines)

    def export_tree(self, filename):
        dot_str = self.gen_dot()
        graphviz.Source(dot_str).render(filename, format="png", cleanup=True)
