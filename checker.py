import problem as pb
import numpy as np
from itertools import combinations


# Checks if the solution is a solution that can be checked
# * right number of elements
# * values in [1,data.nbMachines]
def checkVector(data: pb.Data, solution: pb.Solution) -> bool:
    # Checking that the solution vector is the right one
    # if verbose:
    #     print("Checking the size of the vector")

    if len(solution.assignment) != data.nbProcess:
        print("The solution does not have the correct size")
        print("Size = ", len(solution.assignment), " vs number of processes = ", data.nbProcess)
        print("Test failed")
        return False
    # else:
    #     if verbose:
    #         print("Test passed")

    # if verbose:
    #     print("Checking that the values in the solution are machine indices")
    for p in range(data.nbProcess):
        if solution.assignment[p] > data.nbMachines or solution.assignment[p] < 0:
            print("The machine ID is wrong for process ", p, " : current value =", solution.assignment[p])
            print("Test failed")
            return False

    # if verbose:
    #     print("Test passed")
    return True


def checkCapacity(data: pb.Data, solution: pb.Solution, verbose: bool) -> bool:
    if verbose:
        print("Checking capacity constraint (without transient)")

    # create a vector with 0 consumption for each machine * resource
    resourceConsumption = np.zeros((data.nbMachines, data.nbResources), dtype=np.int64)

    ok = True
    for r in range(data.nbResources):  # for each resource
        # computing the resource consumption of the processes on each machine
        for p in range(data.nbProcess):  # for each process
            # add its resource consumption for the machine to which it is assigned
            resourceConsumption[solution.assignment[p], r] += data.processReq[p, r]
            # checking hard resource consumption for each machine
        for m in range(data.nbMachines):
            if resourceConsumption[m, r] > data.hardResCapacities[m, r]:
                print("Capacity violation for machine ", m, " and resource ", r)
                print(resourceConsumption[m, r], " > ", data.hardResCapacities[m, r])
                ok = False

    if verbose:
        if ok:
            print("Test passed")
        else:
            print("Test failed")

    if verbose:
        print("Checking capacity constraint (with transient)")

    for r in range(data.nbResources):  # for each resource
        if data.transientStatus[r] == 1:  # if it is transient
            # compute the resource consumption (including processes that were originally assigned to the machine )
            for p in range(data.nbProcess):
                if solution.assignment[p] != data.initialAssignment[p]:  # if the process has moved
                    resourceConsumption[data.initialAssignment[p], r] += data.processReq[p,
                                                                                         r]  # add its resource consumption
            # checking hard resource consumption for each machine (including transient processes)
            for m in range(data.nbMachines):
                if resourceConsumption[m, r] > data.hardResCapacities[m, r]:
                    print("When transient resources considered, capacity violation for machine ", m, " and resource ",
                          r)
                    print(resourceConsumption[m, r], " > ", data.hardResCapacities[m, r])
                    ok = False

    if verbose:
        if ok:
            print("Test passed")
        else:
            print("Test failed")
    return ok


def checkConflict(data: pb.Data, solution: pb.Solution, verbose: bool) -> bool:
    if verbose:
        print("Checking disjunctions between processes of the same service")

    ok = True
    processesOfService = np.frompyfunc(list, 0, 1)(np.empty(data.nbServices, dtype=object))
    for p in range(data.nbProcess):
        processesOfService[data.servicesProcess[p]].append(p)

    for s in range(data.nbServices):
        for (i, j) in combinations(processesOfService[s], 2):
            # if i and j are in the same service and on the same machine there is a problem
            if solution.assignment[i] == solution.assignment[j]:
                print("Disjunction constraint violation between processes ", i, " and ", j)
                print("Both belong to service", s, " and are assigned to machine ",
                      solution.assignment[i])
                ok = False

    if verbose:
        if ok:
            print("Test passed")
        else:
            print("Test failed")
    return ok


def checkSpread(data: pb.Data, solution: pb.Solution, verbose: bool) -> bool:
    if verbose:
        print("Checking spread constraints ")
    ok = True
    processesOfService = np.frompyfunc(list, 0, 1)(np.empty(data.nbServices, dtype=object))
    for p in range(data.nbProcess):
        processesOfService[data.servicesProcess[p]].append(p)

    for s in range(data.nbServices):  # for each service
        if data.spreadMin[s] != 0:  # if it has a spread min
            locationsWithService = np.zeros(data.nbLocations,
                                            dtype=np.int64)  # table used to know which locations have service s
            for p in processesOfService[s]:  # for each process of service s
                locationsWithService[
                    data.locations[solution.assignment[p]]] = 1  # note that its current location has its service
            nbLocationsWithService = sum(locationsWithService)  # number of locations with this service
            if nbLocationsWithService < data.spreadMin[s]:  # should be larger than the spread
                print("Spread constraint violated for service ", s)
                print("Present in ", nbLocationsWithService, " locations < ", data.spreadMin[s])
                ok = False

    if verbose:
        if ok:
            print("Test passed")
        else:
            print("Test failed")
    return ok


def checkDependency(data: pb.Data, solution: pb.Solution, verbose: bool) -> bool:
    if verbose:
        print("Checking dependency constraints")
    ok = True

    # table indicating for each neighborhood if it currently has the service
    servicesInNeighborhood = np.zeros((data.nbServices, data.nbNeighborhoods), dtype=np.int64)

    for p in range(data.nbProcess):
        servicesInNeighborhood[data.servicesProcess[p], data.neighborhoods[solution.assignment[p]]] = 1

    for s in range(data.nbServices):
        for n in range(data.nbNeighborhoods):
            for d in data.dependencies[s]:
                # there cannot be s and not t
                if servicesInNeighborhood[s, n] == 1 and servicesInNeighborhood[d, n] == 0:
                    print("Dependency constraint violation")
                    print("Service ", s, " is in neighborhood ", n, " while service ", d, " is not")
                    ok = False

    if verbose:
        if ok:
            print("Test passed")
        else:
            print("Test failed")
    return ok


# Checks that the given solution is feasible
# Return True if the solution is feasible, False otherwise
def checkConstraints(data: pb.Data, solution: pb.Solution, verbose: bool) -> bool:
    # Printing the arguments
    if verbose:
        print("-> Checking the feasibility of the solution ")

    if not checkVector(data, solution):
        print("ERROR: Cannot check the solution")
        return False

    ok = True
    ok = checkCapacity(data, solution, verbose) and ok
    ok = checkConflict(data, solution, verbose) and ok
    ok = checkSpread(data, solution, verbose) and ok
    ok = checkDependency(data, solution, verbose) and ok

    if verbose:
        if ok:
            print("All tests passed: the solution is feasible ")
        else:
            print("ERROR: One or several tests failed: the solution is infeasible")

    return ok


def computeLoadCost(data: pb.Data, solution: pb.Solution) -> int:
    val = 0

    # resource consumption for each machine and each resource
    resourceConsumption = np.zeros((data.nbMachines, data.nbResources), dtype=np.int64)
    for r in range(data.nbResources):
        for p in range(data.nbProcess):
            resourceConsumption[solution.assignment[p], r] += data.processReq[p, r]

    # compute the load cost by summing the cost over machines and resources
    for m in range(data.nbMachines):
        for r in range(data.nbResources):
            # the cost is accounted only if is larger than 0
            if data.weightLoadCost[r] * max(0, resourceConsumption[m, r] - data.softResCapacities[m, r] > 0):
                print('Machine ', m, ' Resource ', r, ' U('+str(m)+','+str(r)+') = ', resourceConsumption[m, r], ' SC('+str(m)+','+str(r)+') = ', data.softResCapacities[m, r], 
                    ' weight = ', data.weightLoadCost[r], ' loadCost = ', data.weightLoadCost[r] * max(0, resourceConsumption[m, r] - data.softResCapacities[m, r]))
            val += data.weightLoadCost[r] * max(0, resourceConsumption[m, r] - data.softResCapacities[m, r])

    return val


def computeBalanceCost(data: pb.Data, solution: pb.Solution) -> int:
    totalBalanceCost = 0

    # for each balance cost data
    for b in data.balanceTriples:
        # table that will contain the remaining capacity for resource r1 on each machine
        slack_r1 = data.hardResCapacities[:, b.resource1].copy()
        # table that will contain the remaining capacity for resource r2 on each machine
        slack_r2 = data.hardResCapacities[:, b.resource2].copy()

        # for each process, remove its resource requirement from the remaining capacity
        for p in range(data.nbProcess):
            slack_r1[solution.assignment[p]] -= data.processReq[p, b.resource1]
            slack_r2[solution.assignment[p]] -= data.processReq[p, b.resource2]

        localBalanceCost = 0  # balance cost for the current value of b
        # sum over all machines of the balance costs
        for m in range(data.nbMachines):
            if max(0, b.target * slack_r1[m] - slack_r2[m]) > 0:
                print('Machine ', m,' ', 'A('+str(m)+','+str(b.resource1)+') = ', slack_r1[m], ' A('+str(m)+','+str(b.resource2)+') = ', slack_r2[m], 
                'target = ', b.target , ' balanceCost = ', max(0, b.target * slack_r1[m] - slack_r2[m]))
            localBalanceCost += max(0, b.target * slack_r1[m] - slack_r2[m])
        totalBalanceCost += b.weight * localBalanceCost

    return totalBalanceCost


def computeProcessMoveCost(data: pb.Data, solution: pb.Solution) -> int:
    val = 0
    # count the number of processes that are not in the same machine after optimizing
    for p in range(data.nbProcess):
        if data.initialAssignment[p] != solution.assignment[p]:
            val += data.processMoveCost[p]
    return val


def computeMachineMoveCost(data: pb.Data, solution: pb.Solution) -> int:
    val = 0
    for p in range(data.nbProcess):
        val += data.machineMoveCosts[data.initialAssignment[p], solution.assignment[p]]
    return val


def computeServiceMoveCost(data: pb.Data, solution: pb.Solution) -> int:
    nbMovesInService = np.zeros(data.nbServices, dtype=np.int64)  # number of processes that moved inside each service
    for p in range(data.nbProcess):
        if data.initialAssignment[p] != solution.assignment[p]:  # if it moved
            nbMovesInService[data.servicesProcess[p]] += 1  # increase the corresponding service counter

    return np.max(nbMovesInService)  # return the maximum among all services


def getCost(data: pb.Data, solution: pb.Solution, verbose: bool) -> float:
    loadCost = computeLoadCost(data, solution)
    balanceCost = computeBalanceCost(data, solution)
    processMoveCost = computeProcessMoveCost(data, solution)
    machineMoveCost = computeMachineMoveCost(data, solution)
    serviceMoveCost = computeServiceMoveCost(data, solution)
    if verbose:
        print("Load cost (computed by the checker) = ", loadCost)
        print("Balance cost (computed by the checker) = ", balanceCost)
        print("Process move cost (computed by the checker) = ", data.processMoveWeight * processMoveCost)
        print("Machine move cost (computed by the checker) = ", data.machineMoveWeight * machineMoveCost)
        print("Service move cost (computed by the checker) = ", data.serviceMoveWeight * serviceMoveCost)
    totalCost = loadCost + balanceCost + data.processMoveWeight * processMoveCost + \
                data.serviceMoveWeight * serviceMoveCost + data.machineMoveWeight * machineMoveCost

    return totalCost


# Checks that the cost stored inside the given solution is correctly computed
# Return True if the cost of the solution is correctly computed, False otherwise
def checkCost(data: pb.Data, solution: pb.Solution, verbose: bool) -> bool:
    # Printing the arguments
    if verbose:
        print("-> Checking the internal cost of solution ")

    if not checkVector(data, solution):
        print("ERROR: Cannot check the solution")
        return False

    totalCost = getCost(data, solution, verbose)

    print("Objective function (computed by the checker) = ", totalCost)
    print("Objective function (recorded in the solution) = ", solution.cost)
    if totalCost != solution.cost:
        print("ERROR: The cost recorded in the solution is not correct (set verbose to True for the detailed values)")


# Checks that the given solution : feasible ? cost correctly computed ?
# Return True if the solution is feasible and its cost is correctly computed, False otherwise
def check(data: pb.Data, solution: pb.Solution, verbose: bool) -> bool:
    feasible = checkConstraints(data, solution, verbose)
    costCorrectlyComputed = checkCost(data, solution, verbose)
    return feasible and costCorrectlyComputed
