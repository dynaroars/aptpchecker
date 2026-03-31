import graphviz

class Node:
    def __init__(self, val, left=None, right=None):
        # Hidden split
        self.val = val # what to display
        self.left: Node = left
        self.right: Node = right

        # Input split
        self.lower_bound = None
        self.upper_bound = None
        self.split_index = None

    def print(self):
        print(f"{self.lower_bound=}")
        print(f"{self.upper_bound=}")

def combine(a: Node, b: Node, split_index):    
    if a.lower_bound[split_index] == b.upper_bound[split_index]:
        left_node = b
        right_node = a
    elif b.lower_bound[split_index] == a.upper_bound[split_index]:
        left_node = a
        right_node = b

    l = left_node.lower_bound[split_index].item()
    m = left_node.upper_bound[split_index].item()
    u = right_node.upper_bound[split_index].item()
    new_node = Node(f"X_{split_index}\n({l}, {u})", left_node, right_node)
    new_node.lower_bound = left_node.lower_bound
    new_node.upper_bound = right_node.upper_bound
    new_node.split_index = split_index

    left_node.val = f"X_{split_index}\n({l}, {m})"
    right_node.val = f"X_{split_index}\n({m}, {u})"
    return new_node

def get_split_index(a: Node, b: Node):
    match_lower = ((a.lower_bound == b.lower_bound) == False).nonzero()
    match_upper = ((a.upper_bound == b.upper_bound) == False).nonzero()

    num_match_lower = match_lower.numel()
    num_match_upper = match_upper.numel()
    if num_match_lower == num_match_upper == 1:
        return match_lower.item()
    return -1

def can_combine(a: Node, b: Node, split_index):
    if split_index == -1:
        return False
    if a.lower_bound[split_index] == b.upper_bound[split_index]:
        return True
    if a.upper_bound[split_index] == b.lower_bound[split_index]:
        return True
    return False

class Group:
    def __init__(self):
        self.split_index = None
        self.splits: list[Node] = []

    def set(self, split_index):
        if self.split_index == None:
            self.split_index = split_index
        else:
            assert self.split_index == split_index, f"{self.splits[-1].lower_bound}"

    def add(self, split):
        self.splits.append(split)

    def _convert_node(self, splits):
        n = len(splits)
        if n == 1:
            return splits[0]
        splits = sorted(splits, key=lambda x: x.lower_bound[self.split_index].item())

        if n == 2:
            left, right = splits
            l = left.lower_bound[self.split_index].item()
            m = left.upper_bound[self.split_index].item()
            u = right.upper_bound[self.split_index].item()
            parent = Node(f"X_{self.split_index}\n({l}, {u})", left, right)
            parent.lower_bound = left.lower_bound
            parent.upper_bound = right.upper_bound
            parent.split_index = self.split_index

            left.val = f"X_{self.split_index}\n({l}, {m})"
            right.val = f"X_{self.split_index}\n({m}, {u})"

        self.print_all()
        print("ok now")
        self.print(splits)
        assert n > 0 and n % 2 == 0
        new_splits = [combine(splits[i], splits[i+1], self.split_index) for i in range(0, n, 2)]
        return self._convert_node(new_splits)

    def convert_node(self):
        return self._convert_node(self.splits)

    def print(self, s):
        print(f"Splits: {self.split_index=}")
        for i, split in enumerate(s):
            print(f"Input {i}: {split.lower_bound=}")
            print(f"Input {i}: {split.upper_bound=}\n")
        print()

    def print_all(self):
        self.print(self.splits)

class BinaryTree:
    def __init__(self, objectives, proof_tree):
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

            return dfs(node.left) + dfs(node.right) + 1

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

            return max(dfs(node.left), dfs(node.right)) + 1

        return dfs(self.root)

    def process(self, nodes):
        groups = []
        for i, node1 in enumerate(nodes):
            if not node1:
                continue
            curr_group = Group()
            curr_group.splits = [node1]

            for j in range(i + 1, len(nodes)):
                node2 = nodes[j]
                if not node2:
                    continue

                split_index = get_split_index(node1, node2)
                if curr_group.split_index != None and curr_group.split_index != split_index:
                    continue
                if can_combine(node1, node2, split_index):
                    curr_group.split_index = split_index
                    curr_group.add(node2)
                    nodes[j] = None # remove it

            groups.append(curr_group)

        new_nodes = []
        for group in groups:
            new_nodes.append(group.convert_node())
        if len(new_nodes) == 1:
            return new_nodes[0]
        return self.process(new_nodes)

    def build_input(self):
        nodes = []
        for ob in self.objectives.objectives:
            new_node = Node("")
            new_node.lower_bound = ob.lower_bound
            new_node.upper_bound = ob.upper_bound
            nodes.append(new_node)

        self.root = self.process(nodes)

    @property
    def num_hidden_proof(self):
        count = dict()
        for proof_step in self.proof_tree:
            for n in proof_step:
                count.setdefault(abs(n), 0)
                count[abs(n)] += 1
        return count

    def build_hidden(self):
        for proof_step in self.proof_tree:
            proof_step = sorted(proof_step, key=lambda x: self.num_hidden_proof[abs(x)], reverse=True)
            self.process_hidden_list(proof_step)

    def process_hidden_list(self, neurons):
        curr: Node = self.root
        for neuron in neurons:
            if neuron < 0:
                if curr.left:
                    assert curr.left.val == neuron, f"{curr.left.val} vs {neuron} in {neurons}"
                else:
                    curr.left = Node(neuron)
                curr = curr.left
            else:
                if curr.right:
                    assert curr.right.val == neuron, f"{curr.right.val} vs {neuron} in {neurons}"
                else:
                    curr.right = Node(neuron)
                curr = curr.right

    def gen_dot(self):
        lines = ["digraph BinaryTree {", "node [shape=circle];"]
        def traverse(node):
            if node is None:
                return
            
            # Use id(node) to uniquely identify nodes
            node_id = id(node)
            lines.append(f'{node_id} [label="{node.val}"];')

            if node.left:
                left_id = id(node.left)
                lines.append(f"{node_id} -> {left_id};")
                traverse(node.left)

            if node.right:
                right_id = id(node.right)
                lines.append(f"{node_id} -> {right_id};")
                traverse(node.right)

        traverse(self.root)
        lines.append("}")
        return "\n".join(lines)

    def export_tree(self, filename):
        dot_str = self.gen_dot()
        graphviz.Source(dot_str).render(filename, format="png", cleanup=True)
