#! usr/bin/python
# -*- coding: utf-8 -*-
from inspect import _void
from modulefinder import Module
from typing import NamedTuple, TypeVar
from mip import *
import itertools

import problem as pb

T = TypeVar('T')

def flatten(l: list[list[T]]) -> list[T]: 
    return list(itertools.chain(*l))

class ProblemVariables(NamedTuple):
    assignments: list[list[Var]]
    initial_assignments: list[list[int]]
    process_is_moving: list[Var]
    assignments_multiplied_by_process_is_moving: list[list[Var]]
    current_assignments: list[list[Var]]
    is_location_contain_service: list[list[Var]]
    process_is_in_neighborhood: list[list[Var]]


def define_variables(data: pb.Data, model: Model):
    return ProblemVariables(
        [[model.add_var(var_type=BINARY, name=f"M(p{i}) = m{j}") for j in range(data.nbMachines)] for i in range(data.nbProcess)],
        [[1 if data.initialAssignment[i] == j else 0 for j in range(data.nbMachines)] for i in range(data.nbProcess)],
        [model.add_var(var_type=BINARY, name=f"isMoving({i})") for i in range(data.nbProcess)],
        [[model.add_var(var_type=BINARY, name=f"(M(p{i}) = m{j}) * isMoving({i})") for j in range(data.nbMachines)] for i in range(data.nbProcess)],
        [[model.add_var(var_type=BINARY, name=f"Mc(p{i}) = m{j}") for j in range(data.nbMachines)] for i in range(data.nbProcess)],
        [[model.add_var(var_type=BINARY, name=f"is_location_contain_service({i})({j})") for j in range(data.nbLocations)] for i in range(data.nbServices)],
        [[model.add_var(var_type=BINARY, name=f"process_is_in_neighborhood({i})({j})") for j in range(data.nbNeighborhoods)] for i in range(data.nbProcess)]
    )

class ProblemConstraints:
    def __init__(self, data: pb.Data, model: Model, vars: ProblemVariables) -> None:
        self.data = data
        self.model = model
        self.vars = vars

    def process_is_assigned_to_only_one_machine(self):
        for a_i, a in enumerate(self.vars.assignments):
            self.model += xsum(a[m] for m in range(self.data.nbMachines)) <= 1, f"process_is_assigned_to_only_one_machine({a_i})"

    def process_is_reassigned_to_a_new_machine(self):
        for a_i, a in enumerate(self.vars.assignments):
            for m_i, (m0, m) in enumerate(zip(self.vars.initial_assignments[a_i], a)):
                self.model += m0 + m <= 1, f"process_is_reassigned_to_a_new_machine({a_i},{m_i})"

    def process_is_moving(self):
        for a_i, a in enumerate(self.vars.assignments):
            self.model += xsum(a[m] for m in range(self.data.nbMachines)) == self.vars.process_is_moving[a_i], f"process_is_moving({a_i})"

    def current_assignments(self):
        for a_i, a in enumerate(self.vars.assignments):
            for m in range(self.data.nbMachines):
                # Linearization of a[m] * self.vars.process_is_moving[a_i]
                self.model += self.vars.assignments_multiplied_by_process_is_moving[a_i][m] <= a[m]
                self.model += self.vars.assignments_multiplied_by_process_is_moving[a_i][m] <= self.vars.process_is_moving[a_i]
                self.model += self.vars.assignments_multiplied_by_process_is_moving[a_i][m] >= a[m] + self.vars.process_is_moving[a_i] - 1
                self.model += (self.vars.assignments_multiplied_by_process_is_moving[a_i][m] + self.vars.initial_assignments[a_i][m] * (1 - self.vars.process_is_moving[a_i])) == self.vars.current_assignments[a_i][m]
    
    def conflicts(self):
        for s in range(self.data.nbServices):
            process_in_service_assignements = [self.vars.current_assignments[p] for p in range(self.data.nbProcess) if self.data.servicesProcess[p] == s]
            for m in range(self.data.nbMachines):
                self.model += xsum(a[m] for a in process_in_service_assignements) <= 1

    def spread(self):
        for s in range(self.data.nbServices):
            process_in_service_assignements = [self.vars.current_assignments[p] for p in range(self.data.nbProcess) if self.data.servicesProcess[p] == s]
            for l in range(self.data.nbLocations):
                process_in_location = flatten([[a[m] for a in process_in_service_assignements] for m in [m for m in range(self.data.nbMachines) if self.data.locations[m] == l]])
                # Linarization of logical OR/max
                for p in process_in_location:
                    self.model += self.vars.is_location_contain_service[s][l] >= p
                self.model += self.vars.is_location_contain_service[s][l] <= xsum(p for p in process_in_location)
                self.model += self.vars.is_location_contain_service[s][l] <= 1
            self.model += xsum(l for l in self.vars.is_location_contain_service[s]) >= self.data.spreadMin[s]
    
    def dependency(self):
        for n in range(self.data.nbNeighborhoods):
            for p in range(self.data.nbProcess):
                self.model += self.vars.process_is_in_neighborhood[p][n] == xsum(self.vars.current_assignments[p][m] for m in range(self.data.nbMachines) if self.data.neighborhoods[m] == n)
        for s in range(self.data.nbServices):
            process_in_service_assignements = [self.vars.process_is_in_neighborhood[p] for p in range(self.data.nbProcess) if self.data.servicesProcess[p] == s]
            process_in_dependent_service_assignements = [self.vars.process_is_in_neighborhood[p] for p in range(self.data.nbProcess) if self.data.servicesProcess[p] == self.data.dependencies[s]]
            for process_a in process_in_service_assignements:
                for process_b in process_in_dependent_service_assignements:
                    for n_a, n_b in zip(process_a, process_b):
                        self.model += n_a == n_b
    def machine_has_enough_capacity(self):
        for m in range(self.data.nbMachines):
            for r in range(self.data.nbResources):
                self.model += xsum(self.vars.current_assignments[p][m] * self.data.processReq[p][r] for p in range(self.data.nbProcess)) <= self.data.hardResCapacities[m][r] #hardResCapacities correspond a la capacité de la machine et non a safeResCapacities

    def transient_usage(self):
        pass

class ProblemObjectives:
    def __init__(self, data: pb.Data, model: Model, vars: ProblemVariables) -> None:
        self.data = data
        self.model = model
        self.vars = vars

    def load_cost(self):
        return xsum(
                xsum(
                    xsum(self.vars.current_assignments[p][m] * self.data.processReq[p,r] for p in range(self.data.nbProcess))
                     - self.data.softResCapacities[m, r] for m in range(self.data.nbMachines)
                ) for r in range(self.data.nbResources)
            )
                
    def total(self): 
        self.model.objective = self.load_cost()

                                             
def solve(data: pb.Data, maxTime: int, verbose: bool) -> pb.Solution:
    model = Model()

    # Variables
    vars = define_variables(data, model)

    # Constraints
    constraints = ProblemConstraints(data, model, vars)
    constraints.process_is_assigned_to_only_one_machine()
    constraints.process_is_reassigned_to_a_new_machine()
    constraints.process_is_moving()
    constraints.current_assignments()
    constraints.machine_has_enough_capacity()
    constraints.conflicts()
    constraints.spread()
    constraints.dependency()
    constraints.transient_usage()

    # Objective
    objective = ProblemObjectives(data, model, vars)   
    objective.total() 

    model.write("model.lp")

    status = model.optimize(max_seconds=maxTime)

    if status == OptimizationStatus.OPTIMAL:
        print('optimal solution cost {} found'.format(model.objective_value))
    elif status == OptimizationStatus.FEASIBLE:
        print('sol.cost {} found, best possible: {}'.format(model.objective_value, model.objective_bound))
    elif status == OptimizationStatus.NO_SOLUTION_FOUND:
        print('no feasible solution found, lower bound is: {}'.format(model.objective_bound))
    if status == OptimizationStatus.OPTIMAL or status == OptimizationStatus.FEASIBLE:
        print('solution:')
        for v in model.vars:
            if abs(v.x) > 1e-6: # only printing non-zeros
                print('{} : {}'.format(v.name, v.x))
    
    return pb.Solution(np.zeros(data.nbProcess), model.objective_value)
