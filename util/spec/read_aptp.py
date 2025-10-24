from beartype import beartype
from copy import deepcopy
import numpy as np
import tqdm
import re

from util.data.objective import Objective
from pysat.solvers import Solver
from pysat.formula import CNF

@beartype
def read_statements(filename: str):
    '''process aptp and return a list of strings (statements)
    useful to get rid of comments and blank lines and combine multi-line statements
    '''
    
    with open(filename, 'r') as f:
        lines = f.readlines()

    lines = [line.strip() for line in lines]
    assert len(lines) > 0

    # combine lines if case a single command spans multiple lines
    open_parentheses = 0
    statements = []
    current_statement = ''

    for line in lines:
        comment_index = line.find(';')

        if comment_index != -1:
            line = line[:comment_index].rstrip()

        if not line:
            continue

        new_open = line.count('(')
        new_close = line.count(')')

        open_parentheses += new_open - new_close

        assert open_parentheses >= 0, "mismatched parenthesis in aptp file"

        # add space
        current_statement += ' ' if current_statement else ''
        current_statement += line

        if open_parentheses == 0:
            statements.append(current_statement)
            current_statement = ''

    if current_statement:
        statements.append(current_statement)

    # remove repeated whitespace characters
    statements = [" ".join(s.split()) for s in statements]

    # remove space after '('
    statements = [s.replace('( ', '(') for s in statements]

    # remove space after ')'
    statements = [s.replace(') ', ')') for s in statements]

    return statements


def update_rv_tuple(rv_tuple, op, first, second, num_inputs, num_outputs):
    'update tuple from rv in read_vnnlib_simple, with the passed in constraint "(op first second)"'

    if first.startswith("X_"):
        # Input constraints
        index = int(first[2:])

        assert not second.startswith("X") and not second.startswith("Y"), \
            f"input constraints must be box ({op} {first} {second})"
        assert 0 <= index < num_inputs, print(index, num_inputs)

        limits = rv_tuple[0][index]

        if op == "<=":
            limits[1] = min(float(second), limits[1])
        else:
            limits[0] = max(float(second), limits[0])

        assert limits[0] <= limits[1], f"{first} range is empty: {limits}"

    elif first.startswith("Y_"):
        # output constraint
        if op == ">=":
            # swap order if op is >=
            first, second = second, first

        row = [0.0] * num_outputs
        rhs = 0.0

        # assume op is <=
        if first.startswith("Y_") and second.startswith("Y_"):
            index1 = int(first[2:])
            index2 = int(second[2:])

            row[index1] = 1
            row[index2] = -1
        elif first.startswith("Y_"):
            index1 = int(first[2:])
            row[index1] = 1
            rhs = float(second)
        else:
            assert second.startswith("Y_")
            index2 = int(second[2:])
            row[index2] = -1
            rhs = -1 * float(first)

        mat, rhs_list = rv_tuple[1], rv_tuple[2]
        mat.append(row)
        rhs_list.append(rhs)

    elif first.startswith("N_"):
        raise NotImplementedError(first)
    else:
        raise ValueError(first)

def make_input_box_dict(num_inputs):
    'make a dict for the input box'

    rv = {i: [-float('inf'), float('inf')] for i in range(num_inputs)}

    return rv


@beartype
def read_input_output(filename: str) -> list:
    # example: "(declare-const X_0 Real)"
    # example: "(declare-const X_0 X_1 Real)"
    regex_declare = re.compile(r"^\(declare-const ((?:X_\S+|Y_\S+)(?:\s+(?:X_\S+|Y_\S+))*) Real\)$")

    # comparison sub-expression
    # example: "(<= Y_0 Y_1)" or "(<= Y_0 10.5)"
    comparison_str = r"\((<=|>=) (\S+) (\S+)\)"

    # example: "(and (<= Y_0 Y_2)(<= Y_1 Y_2))"
    cnf_clause_str = r"\(and\s*(" + comparison_str + r")+\)"

    # example: "(assert (<= Y_0 Y_1))"
    regex_simple_assert = re.compile(r"^\(assert " + comparison_str + r"\)$")

    # disjunctive-normal-form
    # (assert (or (and (<= Y_3 Y_0)(<= Y_3 Y_1)(<= Y_3 Y_2))(and (<= Y_4 Y_0)(<= Y_4 Y_1)(<= Y_4 Y_2))))
    regex_dnf = re.compile(r"^\(assert \(or (" + cnf_clause_str + r")+\)\)$")

    lines = read_statements(filename)

    # Read lines to determine number of inputs and outputs
    num_inputs = num_outputs = 0

    for line in lines:
        declares = regex_declare.findall(line)
        # print(line, declares)
        if len(declares) == 0:
            continue
        elif len(declares) > 1:
            raise ValueError(f'There cannot be more than one declaration in one line: {line}')
        else:
            for declare in declares[0].split():
                # print(declare)
                declare = declare.split('_')
                if declare[0] == 'X':
                    num_inputs = max(num_inputs, int(declare[1]) + 1)
                elif declare[0] == 'Y':
                    num_outputs = max(num_outputs, int(declare[1]) + 1)
                else:
                    raise ValueError(f'Unknown declaration: {line}')
                
    print(f'[!] APTP: {num_inputs=}, {num_outputs=}')
    rv = []  # list of 3-tuples, (box-dict, mat, rhs)
    rv.append((make_input_box_dict(num_inputs), [], []))

    for line in lines:
        if len(regex_declare.findall(line)) > 0:
            continue

        groups = regex_simple_assert.findall(line)

        if groups:
            assert len(groups[0]) == 3, f"groups was {groups}: {line}"
            op, first, second = groups[0]

            for rv_tuple in rv:
                update_rv_tuple(rv_tuple, op, first, second, num_inputs, num_outputs)

            continue
        
        groups = regex_dnf.findall(line)
        ################
        if not groups:
            # print(f"[APTP] Skipped parsing line: {line}.")
            continue

        tokens = line.replace("(", " ").replace(")", " ").split()
        tokens = tokens[2:]  # skip 'assert' and 'or'

        conjuncts = " ".join(tokens).split("and")[1:]
        old_rv = rv
        rv = []

        for rv_tuple in old_rv:
            if len(conjuncts) > 10:
                pbar = tqdm.tqdm(conjuncts)
            else:
                pbar = conjuncts

            for c in pbar:
                rv_tuple_copy = deepcopy(rv_tuple)
                rv.append(rv_tuple_copy)

                c_tokens = [s for s in c.split(" ") if len(s) > 0]

                count = len(c_tokens) // 3

                for i in range(count):
                    op, first, second = c_tokens[3 * i:3 * (i + 1)]

                    update_rv_tuple(rv_tuple_copy, op, first, second, num_inputs, num_outputs)

    # merge elements of rv with the same input spec
    merged_rv = {}

    for rv_tuple in rv:
        boxdict = rv_tuple[0]
        matrhs = (rv_tuple[1], rv_tuple[2])

        key = str(boxdict)  # merge based on string representation of input box... accurate enough for now

        if key in merged_rv:
            merged_rv[key][1].append(matrhs)
        else:
            merged_rv[key] = (boxdict, [matrhs])

    # finalize objects (convert dicts to lists and lists to np.array)
    final_rv = []

    for rv_tuple in merged_rv.values():
        box_dict = rv_tuple[0]

        box = []

        for d in range(num_inputs):
            r = box_dict[d]

            assert r[0] != -np.inf and r[1] != np.inf, f"input X_{d} was unbounded: {r}"
            box.append(r)

        spec_list = []

        for matrhs in rv_tuple[1]:
            mat = np.array(matrhs[0], dtype=float)
            rhs = np.array(matrhs[1], dtype=float)
            spec_list.append((mat, rhs))

        final_rv.append((box, spec_list))

    return final_rv


def extract_and_clauses(logical_expression):
    and_clause_pattern = re.compile(r'\(and\s+((?:\([^\)]+\)\s*)+)\)')
    and_clauses = and_clause_pattern.findall(logical_expression)
    result = [re.findall(r'\([^\)]+\)', clause) for clause in and_clauses]
    return result

@beartype
def read_hidden(filename: str) -> list:    
    # example: "(declare-const X_0 Real)"
    # regex_declare = re.compile(r"^\(declare-pwl (N_\S+) (\S+)\)$")
    regex_declare = re.compile(r"^\(declare-pwl ((?:N_\S+)(?:\s+(?:N_\S+))*) (\S+)\)$")

    # comparison sub-expression
    # example: "(< N_2 0)" or "(>= N_4 0))"
    comparison_str = r"\((<|>=) (\S+) (\S+)\)"

    # example: "(and (< N_2 0)(>= N_4 0))"
    cnf_clause_str = r"\(and\s*(" + comparison_str + r")+\)"

    # disjunctive-normal-form
    # (assert (or (and (< N_4 0))(and (< N_2 0)(>= N_4 0))(and (>= N_2 0)(>= N_1 0)(>= N_4 0))(and (>= N_2 0)(< N_1 0)(>= N_4 0))))
    regex_dnf = re.compile(r"^\(assert \(or (" + cnf_clause_str + r")+\)\)$")

    lines = read_statements(filename)

    # extract activation
    declared_neuron_names = []
    for line in lines:
        declares = regex_declare.findall(line)
        if len(declares) == 0:
            continue
        elif len(declares) > 1:
            raise ValueError(f'There cannot be more than one declaration in one line: {line}')
        else:
            declares = declares[0]
            # FIXME: generalize for other activation functions
            assert declares[1].lower() == 'relu', f'Invalid {declares[1]}'
            for declare in declares[0].split():
                if declare.startswith('N'):
                    declared_neuron_names.append(declare)
                else:
                    raise ValueError(f'Unknown declaration: {line}')
    declared_neuron_names = list(sorted(set(declared_neuron_names)))
    num_neurons = len(declared_neuron_names)
    print(f'[!] APTP: {num_neurons=}')
    
    and_clauses = []
    for line in lines:
        groups = regex_dnf.findall(line)
        if groups:
            # print(f'{line=}')
            and_clauses += extract_and_clauses(line)
      
    proof = []      
    for clause in tqdm.tqdm(and_clauses, desc='Extracting proof tree'):
        node = []
        for item in clause:
            direction, neuron_name, point = item.replace('(', '').replace(')', '').split()
            print(f'{direction=}, {neuron_name=}, {point=}')
            if point.startswith('Y'):
                continue
            assert float(point) == 0, f'Invalid {point=}'
            assert neuron_name in declared_neuron_names, f'Invalid {neuron_name=} {declared_neuron_names=}'
            neuron_id = int(neuron_name.split('_')[1])
            if '>=' in direction:
                node.append(neuron_id)
            else:
                node.append(-neuron_id)
        if node:
            proof.append(node)
    return proof

@beartype
def read_aptp(filename: str) -> tuple[list[Objective], list]:
    print(f'\n############ Extract APTP ############\n')
    assert filename.endswith('.aptp'), filename
    # extract proof tree
    proof = read_hidden(filename)
    print(f'{proof=}')
    assert len(proof) > 0
    
    # extract input and output properties
    in_out = read_input_output(filename)
    assert len(in_out) == 1
    
    bounds = in_out[0][0]
    objectives = []
    for out in in_out[0][1]:
        objective = Objective((bounds, out))
        objectives.append(objective)
        
    # validate
    cnf = CNF(from_clauses=proof)
    with Solver(bootstrap_with=cnf) as solver:
        assert not solver.solve(), f'Invalid proof syntax: {proof=}'
    
    return objectives, proof