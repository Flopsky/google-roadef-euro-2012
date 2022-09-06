#! usr/bin/python
# -*- coding: utf-8 -*-
import sys
import problem as pb
import numpy as np


def parseFiles(dataFileName: str, assignmentFileName: str) -> pb.Data:
    if isinstance(dataFileName, str):  # if fileName is a string
        # open the file, close it automatically at the end of the loop, and handle exceptions
        with open(dataFileName, "r") as file:
            # RESOURCES
            line = file.readline()  # next line
            nbResources = int(line)
            transientStatus = np.empty(nbResources, dtype=int)
            weightLoadCost = np.empty(nbResources, dtype=int)
            for r in range(nbResources):
                line = file.readline()  # next line
                chunks = line.split(' ')  # split the line using a single space as the separator
                transientStatus[r] = int(chunks[0])
                weightLoadCost[r] = int(chunks[1])

            # MACHINES
            line = file.readline()
            nbMachines = int(line)
            neighborhoods = np.empty(nbMachines, dtype=int)
            locations = np.empty(nbMachines, dtype=int)
            hardResCapacities = np.empty((nbMachines, nbResources), dtype=int)
            softResCapacities = np.empty((nbMachines, nbResources), dtype=int)
            machineMoveCosts = np.empty((nbMachines, nbMachines), dtype=int)
            for m in range(nbMachines):
                line = file.readline()
                chunks = line.split(' ')
                neighborhoods[m] = int(chunks[0])
                locations[m] = int(chunks[1])
                for i in range(2, 2 + nbResources):
                    hardResCapacities[m, i - 2] = int(chunks[i])
                for i in range(2 + nbResources, 2 + 2 * nbResources):
                    softResCapacities[m, i - 2 - nbResources] = int(chunks[i])
                for i in range(2 + 2 * nbResources, 2 + 2 * nbResources + nbMachines):
                    machineMoveCosts[m, i - 2 - 2 * nbResources] = int(chunks[i])

            # SERVICES
            line = file.readline()
            nbServices = int(line)
            spreadMin = np.empty(nbServices, dtype=int)
            dependencies = np.empty(nbServices, dtype=list)
            for s in range(nbServices):
                line = file.readline()
                chunks = line.split(' ')
                spreadMin[s] = int(chunks[0])
                nbDependenciesCurS = int(chunks[1])
                dependencies[s] = []
                if nbDependenciesCurS != 0:
                    for i in range(2, 2 + nbDependenciesCurS):
                        dependencies[s].append(int(chunks[i]))

            # PROCESSES
            line = file.readline()
            nbProcess = int(line)
            servicesProcess = np.empty(nbProcess, int)
            processRequirement = np.empty((nbProcess, nbResources), int)
            processMoveCost = np.empty(nbProcess, int)
            for p in range(nbProcess):
                line = file.readline()
                chunks = line.split(' ')
                servicesProcess[p] = int(chunks[0])
                for i in range(1, 1 + nbResources):
                    processRequirement[p, i - 1] = int(chunks[i])
                processMoveCost[p] = int(chunks[1 + nbResources])

            # BALANCE
            line = file.readline()
            nbBalanceTriples = int(line)
            if nbBalanceTriples > 1:
                sys.exit("Only 0 or 1 balance constraint in the files")
            balanceTriples = np.empty(nbBalanceTriples, dtype=pb.BalanceTriple)
            for b in range(nbBalanceTriples):
                line = file.readline()
                chunks = line.split(' ')
                balanceTriple = np.empty(3, dtype=int)
                for i in range(3):
                    balanceTriple[i] = (int(chunks[i]))
                line = file.readline()
                balanceCostWeight = int(line)
                balanceTriples[b] = pb.BalanceTriple(balanceTriple[0], balanceTriple[1],
                                                     balanceTriple[2], balanceCostWeight)

            # MOVE WEIGHTS
            line = file.readline()
            chunks = line.split(' ')
            processMoveWeight = int(chunks[0])
            serviceMoveWeight = int(chunks[1])
            machineMoveWeight = int(chunks[2])

    if isinstance(assignmentFileName, str):
        with open(assignmentFileName, "r") as file:
            initialAssignment = np.empty(nbProcess, dtype=int)
            line = file.readline()
            chunks = line.split(' ')
            for i in range(nbProcess):
                initialAssignment[i] = int(chunks[i])

    data = pb.Data(nbResources, transientStatus, weightLoadCost,
                   nbMachines, neighborhoods, len(neighborhoods), locations, len(locations),
                   softResCapacities, hardResCapacities, machineMoveCosts,
                   nbServices, spreadMin, dependencies,
                   nbProcess, servicesProcess, processRequirement, processMoveCost,
                   nbBalanceTriples, balanceTriples,
                   processMoveWeight, serviceMoveWeight, machineMoveWeight,
                   initialAssignment)

    return data


def parseSolutionFile(data: pb.Data, solutionFileName: str) -> pb.Solution:
    if isinstance(solutionFileName, str):
        with open(solutionFileName, "r") as file:
            assignment = np.empty(data.nbProcess, dtype=int)
            line = file.readline()
            chunks = line.split(' ')
            for i in range(data.nbProcess):
                assignment[i] = int(chunks[i])

    solution = pb.Solution(assignment,0.0)
    return solution
