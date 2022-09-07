#! usr/bin/python
# -*- coding: utf-8 -*-
from inspect import _void
from typing import NamedTuple
from mip import *
import numpy as np

import problem as pb

class ProblemVariables(NamedTuple):
    assignments: list[list[Var]]
    initial_assignments: list[list[int]]

def define_variables(data: pb.Data, m: Model):
    return ProblemVariables(
        [[m.add_var(var_type=BINARY, name=f"M(p{i}) = m{j}") for j in range(data.nbMachines)] for i in range(data.nbProcess)],
        [[1 if data.initialAssignment[i] == j else 0 for j in range(data.nbMachines)] for i in range(data.nbProcess)],
    )

def constraint_process_is_assigned_to_only_one_machine(data: pb.Data, m: Model, vars: ProblemVariables):
    for i, a in enumerate(vars.assignments):
        m += xsum(a[j] for j in range(data.nbMachines)) <= 1, constraint_process_is_assigned_to_only_one_machine.__name__ + f"({i})"

def solve(data: pb.Data, maxTime: int, verbose: bool) -> pb.Solution:
    m = Model()

    vars = define_variables(data, m)
    constraint_process_is_assigned_to_only_one_machine(data, m, vars)
    
    return pb.Solution(np.zeros(data.nbProcess), m.objective_value)
