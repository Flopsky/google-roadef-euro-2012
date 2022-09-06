#! usr/bin/python
# -*- coding: utf-8 -*-
import sys

from typing import NamedTuple, Any
from nptyping import NDArray, Shape, Int


# A python namedtuple is immutable. We can’t change its attributes
class BalanceTriple(NamedTuple):
    resource1: int  # first resource
    resource2: int  # second resource
    target: int  # target aimed for the resource consumption
    weight: int  # weight of the balance triple


# ----------------------------------------------------------------------------
#  data structure for an instance of Google challenge problem
# ----------------------------------------------------------------------------
class Data(NamedTuple):
    nbResources: int  # number of resources |R|
    transientStatus: NDArray[Shape["*"], Int]  # transientStatus[r] is 1 if resource r is transient, 0 otherwise
    weightLoadCost: NDArray[Shape["*"], Int]  # weightLoadCost[r] indicating the weight of load cost for each resource

    nbMachines: int  # number of machines |M|
    neighborhoods: NDArray[Shape["*"], Int]  # neighborhoods[m] is equal to the neighborhood to which machine m belongs
    nbNeighborhoods: int  # total number of neighborhoods
    locations: NDArray[Shape["*"], Int]  # locations[m] is equal to the location of machine m
    nbLocations: int  # total number of locations
    softResCapacities: NDArray[
        Shape["*,*"], Int]  # softResCapacities[m,r] is equal to SC(m,r)
    hardResCapacities: NDArray[
        Shape["*,*"], Int]  # hardResCapacities[m,r] is equal to Cds(m,r)
    machineMoveCosts: NDArray[Shape["*,*"], Int]  # machineMoveCosts[m1,m2] is equal to MMC(m1,m2)

    nbServices: int  # number of services |S|
    spreadMin: NDArray[Shape["*"], Int]  # spreadMin[s] is equal to spreadMin(s) (i.e., the minimum number of distinct locations where at least one process of service s should run)
    dependencies: NDArray[Shape["*"], Any]  # dependencies[s] is the list of services on which service s depends

    nbProcess: int  # number of processes |P|
    servicesProcess: NDArray[Shape["*"], Int]  # servicesProcess[p] is the service to which process p belongs
    processReq: NDArray[Shape["*,*"], Int]  # processResReq[p,r] is equal to R(p,r)
    processMoveCost: NDArray[Shape["*"], Int]  # processMoveCost[p] is equal to PMC(p)

    nbBalanceTriples: int  # number of balance triples |B|
    balanceTriples: NDArray[Shape["*"], Any]  # balanceTriples[b] is the triple b (object of type BalanceTriple)
    processMoveWeight: int  # weight for the process move cost
    serviceMoveWeight: int  # weight for the service move cost
    machineMoveWeight: int  # weight for the machine move cost

    initialAssignment: NDArray[Shape["*"], Int]  # initialAssignment[p] is equal to M0(p)


class Solution(NamedTuple):
    assignment: NDArray[Shape["*"], Int]  # assignment[p] is the machine to which the process p is assigned.
    cost: int  # value of the objective function


def printData(data: Data):
    print("-------------------------------")
    print("### Resources ###")
    print("nb resources = ", data.nbResources)
    print("transient status = ", data.transientStatus)
    print("weight of load cost = ", data.weightLoadCost)

    print("\n### Machines ###")
    print("nbMachines = ", data.nbMachines)
    print("Neighborhoods = ", data.neighborhoods)
    print("Locations = ", data.locations)
    print("Hard cap = ", data.hardResCapacities)
    print("Soft cap = ", data.softResCapacities)
    print("Machine move costs = ", data.machineMoveCosts)

    print("\n### Services ###")
    print("Number of services = ", data.nbServices)
    print("Minimum spread = ", data.spreadMin)
    print("Dependencies = ")
    lineCount = 0
    for dependency in data.dependencies:
        lineCount += 1
        if lineCount % 20 == 0:
            print("")
        print(dependency, end="")

    print("\n### Processes ###")
    print("Number of processes = ", data.nbProcess)
    print("Process Services = ", data.servicesProcess)
    print("Process requirement = ", data.processReq)
    print("Process move cost = ", data.processMoveCost)

    print("\n### Objective function ###")
    print("Nb balance triples for balance cost = ", data.nbBalanceTriples)
    print("Balance triples = ", data.balanceTriples)
    print("Process move weight : ", data.processMoveWeight)
    print("Service move weight : ", data.serviceMoveWeight)
    print("Machine move weight : ", data.machineMoveWeight)

    print("\n### Initial assignment ###")
    print("Initial assignment : ", data.initialAssignment)

    print("-------------------------------")
