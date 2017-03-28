# Submitter: tryond(tryon, daniel) 20621204
# Partner: joshuaek(klein, joshua) 58485794

import filereader
import gameboard
import variable
import domain
import trail
import constraint
import constraintnetwork
import time
from collections import defaultdict
import Queue

import itertools

# dictionary mapping heuristic to number
'''

for example, to set the variable selection heuristic to MRV,
you would say,
self.setVariableSelectionHeuristic(VariableSelectionHeuristic['MinimumRemainingValue'])
this is needed when you have more than one heuristic to break ties or use one over the other in precedence.
you can also manually set the heuristics in the main.py file when reading the parameters
as the primary heuristics to use and then break ties within the functions you implement
It follows similarly to the other heuristics and chekcs
'''
VariableSelectionHeuristic = {'None': 0, 'MRV': 1, 'DH': 2}
ValueSelectionHeuristic = {'None': 0, 'LCV': 1}
ConsistencyCheck = {'None': 0, 'ForwardChecking': 1, 'ArcConsistency': 2}
HeuristicCheck = {'None': 0, 'NKP': 1, 'NKT': 2}

MIN_DOMAIN = 2

class BTSolver:
    "Backtracking solver"

    ######### Constructors Method #########
    def __init__(self, gb):
        self.network = filereader.GameBoardToConstraintNetwork(gb)
        self.trail = trail.masterTrailVariable
        self.hassolution = False
        self.gameboard = gb

        self.maxDegree = ((gb.N-1) * 2) + ((gb.p-1) * (gb.q-1))

        self.numAssignments = 0
        self.numBacktracks = 0
        self.preprocessing_startTime = 0
        self.preprocessing_endTime = 0
        self.startTime = None
        self.endTime = None

        self.varHeuristics = 0  # refers to which variable selection heuristic in use(0 means default, 1 means MRV, 2 means DEGREE)
        self.valHeuristics = 0  # refers to which value selection heuristic in use(0 means default, 1 means LCV)
        self.cChecks = 0  # refers to which consistency check will be run(0 for backtracking, 1 for forward checking, 2 for arc consistency)
        self.heuristicChecks = 0
        # self.runCheckOnce = False
        self.tokens = []  # tokens(heuristics to use)

    ######### Modifiers Method #########

    def setTokens(self, tokens):
        ''' set the set of heuristics to be taken into consideration'''
        self.tokens = tokens

    def setVariableSelectionHeuristic(self, vsh):
        '''modify the variable selection heuristic'''
        self.varHeuristics = vsh

    def setValueSelectionHeuristic(self, vsh):
        '''modify the value selection heuristic'''
        self.valHeuristics = vsh

    def setConsistencyChecks(self, cc):
        '''modify the consistency check'''
        self.cChecks = cc

    def setHeuristicChecks(self, hc):
        '''modify the heurisic check (naked pairs and triples)'''
        self.heuristicChecks += hc

    ######### Accessors Method #########
    def getSolution(self):
        return self.gameboard

    # @return time required for the solver to attain in seconds
    def getTimeTaken(self):
        return self.endTime - self.startTime

    ######### Helper Method #########
    def checkConsistency(self):
        '''which consistency check to run but it is up to you when implementing the heuristics to break ties using the other heuristics passed in'''
        if self.cChecks == 0:
            return self.assignmentsCheck()
        elif self.cChecks == 1:
            return self.forwardChecking()
        elif self.cChecks == 2:
            return self.arcConsistency()
        else:
            return self.assignmentsCheck()

    def checkHeuristics(self):
        if self.heuristicChecks == 1:
            return self.nakedPairs()
        elif self.heuristicChecks == 2:
            return self.nakedTriples()
        elif self.heuristicChecks == 3:
            return self.nakedPairs() and self.nakedTriples()
        else:
            return True    

    def assignmentsCheck(self):
        """
            default consistency check. Ensures no two variables are assigned to the same value.
            @return true if consistent, false otherwise.
        """
        for v in self.network.variables:
            if v.isAssigned():
                for vOther in self.network.getNeighborsOfVariable(v):
                    if v.getAssignment() == vOther.getAssignment():
                        return False
        return True


    def nakedPairs(self):

        ################################################################
        # True if eliminate val from neighbors' domains upon assignment
        propagate = False
        ################################################################

        # set of all contraints to check
        constraint_set = set(self.network.constraints)

        # constraint: each row, column, and block
        while len(constraint_set) > 0:

            # get row, column, or block
            constraint = constraint_set.pop()

            # for all cells in constraint with domain size of 2
            for var_a, var_b in itertools.combinations([x for x in constraint.vars if x.domain.size() == 2], 2):

                # if domains are the same, pair found
                if set(var_a.Values()) == set(var_b.Values()):

                    # var_c: variable to remove values from
                    for var_c in constraint.vars:

                        # variable must be outside of pair
                        if var_a is var_c or var_b is var_c:
                            continue

                        altered_domain = False
                        old_domain_size = var_c.domain.size()

                        # all values to remove from variables in constraint
                        for val in var_a.domain.values:

                            # if var is already assigned with the val to elim, inconsistency detected
                            if var_c.isAssigned() and var_c.getAssignment() == val:
                                return False

                            # attempt to remove from var_c
                            var_c.removeValueFromDomain(val)

                        # if size difference, then domain has been altered
                        altered_domain = var_c.domain.size() != old_domain_size

                        # if new cell is potentially part of naked pair, add constraints to set
                        if altered_domain and var_c.domain.size() == 2:
                            for c in self.network.getConstraintsContainingVariable(var_c):
                                constraint_set.add(c)

                        # DEBUG: Assignment has been made
                        if propagate and altered_domain and var_c.isAssigned():

                            # not adding potential naked pair cells...
                            consistent = self.forwardChecking()
                            if not consistent:
                                print("INC")
                                return False

        return True


    def nakedTriples(self):

        ################################################################
        # True if eliminate val from neighbors' domains upon assignment
        propagate = False
        ################################################################

        # set of all contraints to check
        constraint_set = set(self.network.constraints)

        # constraint: each row, column, and block
        while len(constraint_set) > 0:

            # get row, column, or block
            constraint = constraint_set.pop()

            # for all cells in constraint with domain.size of 3 or less
            for var_a, var_b in itertools.combinations([x for x in constraint.vars if x.domain.size() <= 3], 2):

                # both variables must be unassigned
                if var_a.isAssigned() or var_b.isAssigned():
                    continue

                # union of domains must equal 3
                prelim_union = set(var_a.domain.values) | set(var_b.domain.values)
                if len(prelim_union) != 3:
                    continue

                # var_c: variable to remove values from
                for var_c in constraint.vars:

                    # variable must be outside of pair
                    if var_a is var_c or var_b is var_c:
                        continue

                    # union of domains must equal 3
                    final_union = prelim_union | set(var_c.domain.values)
                    if len(final_union) != 3:
                        continue

                    # var_d: variable to remove values from
                    for var_d in constraint.vars:

                        # variable must be outside of triple
                        if var_a is var_d or var_b is var_d or var_c is var_d:
                            continue

                        altered_domain = False
                        old_domain_size = var_d.domain.size()

                        # all values to remove from variables in constraint
                        for val in final_union:

                            # if var is already assigned with the val to elim, inconsistency detected
                            if var_d.isAssigned() and var_d.getAssignment() == val:
                                return False

                            # Attempt to remove from var_d
                            var_d.removeValueFromDomain(val)

                        # if size difference, then domain has been altered
                        altered_domain = var_d.domain.size() != old_domain_size

                        # if new cell is potentially part of naked pair, add constraints to set
                        if altered_domain and var_c.domain.size() <= 3 and not var_c.isAssigned():
                            for c in self.network.getConstraintsContainingVariable(var_d):
                                constraint_set.add(c)

                        # DEBUG: Assignment has been made
                        if propagate and altered_domain and var_d.isAssigned():

                            # not adding potential naked pair cells...
                            consistent = self.forwardChecking()
                            if not consistent:
                                print("INC")
                                return False

        return True

    # Forward Checking: If you assign a variable X, if another variable Y is involved in a constraint with X, you prune
    # the domain of Y with any inconsistent values
    def forwardChecking(self):

        # set of vars to check
        to_check = set()

        # get last var modified
        vPair = self.trail.trailStack[-1]
        v = vPair[0]

        # if last var modified not assigned, return
        if not v.isAssigned():
            return True

        # add last var to set
        to_check.add(v)

        while len(to_check) > 0:

            # pick last variable assigned, v
            var = to_check.pop()
            val = var.getAssignment()

            # get all neighbors that have not been assigned yet
            for neighbor in self.network.getNeighborsOfVariable(var):

                # if neighbor is assigned with var to elim, inconsistency detected
                if neighbor.isAssigned() and neighbor.getAssignment() == val:
                    return False

                # attempt to remove var value from neighbor domain
                old_domain_size = neighbor.domain.size()
                neighbor.removeValueFromDomain(val)
                domain_altered = neighbor.domain.size() != old_domain_size

                # if the neighbor has been assigned, add to to_check set
                if neighbor.isAssigned() and domain_altered:
                    to_check.add(neighbor)

        return True

    # Arc Consistency: For every pair of variables participating in constraints with each other, every value in one
    # variable's domain must be satisfiable by at least one value in the other variable's domain.
    def arcConsistency(self):

        # set of vars to check
        to_check = set()

        # add all assigned variables to the set
        for v in self.network.variables:
            if v.isAssigned():
                to_check.add(v)

        while len(to_check) > 0:

            # get next variable to check
            y = to_check.pop()
            val = y.getAssignment()

            # get all neighbors of the assigned var
            for x in self.network.getNeighborsOfVariable(y):

                # if x is assigned with val to elim, inconsistency detected
                if x.isAssigned() and x.getAssignment() == y.getAssignment():
                    return False

                # attempt to remove y value from x domain
                old_domain_size = x.domain.size()
                x.removeValueFromDomain(val)
                domain_altered = x.domain.size() != old_domain_size

                # if x has been assigned, add to to_check set
                if x.isAssigned() and domain_altered:
                    to_check.add(x)

        return True

    def selectNextVariable(self):
        """
            Selects the next variable to check.
            @return next variable to check. null if there are no more variables to check.
        """
        if self.varHeuristics == 0:
            return self.getfirstUnassignedVariable()
        elif self.varHeuristics == 1:
            return self.getMRV()
        elif self.varHeuristics == 2:
            return self.getDegree()
        else:
            return self.getfirstUnassignedVariable()

    def getfirstUnassignedVariable(self):
        """
            default next variable selection heuristic. Selects the first unassigned variable.
            @return first unassigned variable. null if no variables are unassigned.
        """
        for v in self.network.variables:
            if not v.isAssigned():
                return v
        return None

    def getMRV(self):

        # set return value to null
        to_ret = None

        # min is set to just above largest possible size
        min = self.gameboard.N + 1

        # visit all cells
        for v in self.network.variables:

            # search for the smallest domain among unassigned cells
            if not v.isAssigned() and v.domain.size() < min:

                # set the new min and return value
                min = v.domain.size()
                to_ret = v

                # return if domain is smallest possible
                if min <= MIN_DOMAIN:
                    return to_ret

        # returns null if all vars assigned
        return to_ret

    def getDegree(self):

        # set return values to null
        to_ret = None

        max = -1
        count = 0

        # visit all cells
        for v in self.network.variables:

            # visit unassigned cells
            if not v.isAssigned():

                # tally number of contraints
                count = len(self.network.getConstraintsContainingVariable(v))

                # if largest, update the return value
                if count > max:
                    max = count
                    to_ret = v

                    # return if degree is largest possible
                    if count >= self.maxDegree:
                        return to_ret

            # reset the degree count
            count = 0

        # returns null if all vars assigned
        return to_ret

    def getNextValues(self, v):
        """
            Value Selection Heuristics. Orders the values in the domain of the variable
            passed as a parameter and returns them as a list.
            @return List of values in the domain of a variable in a specified order.
        """
        if self.valHeuristics == 0:
            return self.getValuesInOrder(v)
        elif self.valHeuristics == 1:
            return self.getValuesLCVOrder(v)
        else:
            return self.getValuesInOrder(v)

    def getValuesInOrder(self, v):
        """
            Default value ordering.
            @param v Variable whose values need to be ordered
            @return values ordered by lowest to highest.
        """
        values = v.domain.values
        return sorted(values)

    def getValuesLCVOrder(self, v):

        # dictionary: { value : # of times appearing in neighbors' domains }
        dict = {x:0 for x in v.domain.values}

        # for all neighbors of variable v
        for neighbor in self.network.getNeighborsOfVariable(v):

            # for every value in neighbor domain
            for val in neighbor.Values():

                # if neighbors' domain includes val, increment score
                try:
                    dict[val] += 1
                except:
                    pass

        # return list of values sorted by # of appearances in neighbors
        return sorted(dict, key=dict.get)

    def success(self):
        """ Called when solver finds a solution """
        self.hassolution = True
        self.gameboard = filereader.ConstraintNetworkToGameBoard(self.network,
                                                                 self.gameboard.N,
                                                                 self.gameboard.p,
                                                                 self.gameboard.q)

    ######### My Helper Methods #########

    # returns set of indices for neighbors of v in same row
    def get_row_indices(self, v):
        min = (v.row - 1) * self.gameboard.N
        return set(range(min,min+self.gameboard.N+1))

    # returns set of indices for neighbors of v in same column
    def get_col_indices(self, v):
        pass

    # returns set of indices for neighbors of v in same block
    def get_block_indices(self, v):
        pass


    ######### Solver Method #########
    def solve(self):
        """ Method to start the solver """
        self.startTime = time.time()
        # try:
        self.solveLevel(0)
        # except:
        # print("Error with variable selection heuristic.")
        self.endTime = time.time()
        # trail.masterTrailVariable.trailStack = []
        self.trail.trailStack = []


    def solveLevel(self, level):
        """
            Solver Level
            @param level How deep the solver is in its recursion.
            @throws VariableSelectionException
        contains some comments that can be uncommented for more in depth analysis
        """
        # print("=.=.=.=.=.=.=.=.=.=.=.=.=.=.=.=")
        # print("BEFORE ANY SOLVE LEVEL START")
        # print(self.network)
        # print("=.=.=.=.=.=.=.=.=.=.=.=.=.=.=.=")

        if self.hassolution:
            return

        # Select unassigned variable
        v = self.selectNextVariable()
        # print("V SELECTED --> " + str(v))

        # check if the assigment is complete
        if (v == None):
            # print("!!! GETTING IN V == NONE !!!")
            for var in self.network.variables:
                if not var.isAssigned():
                    raise ValueError("Something happened with the variable selection heuristic")
            self.success()
            return

        # loop through the values of the variable being checked LCV
        # print("getNextValues(v): " + str(self.getNextValues(v)))
        for i in self.getNextValues(v):
            # print("next value to test --> " + str(i))
            self.trail.placeTrailMarker()

            # check a value
            # print("-->CALL v.updateDomain(domain.Domain(i)) to start to test next value.")
            v.updateDomain(domain.Domain(i))
            self.numAssignments += 1

            # move to the next assignment
            if self.checkConsistency() and self.checkHeuristics():
                self.solveLevel(level + 1)

            # if this assignment failed at any stage, backtrack
            if not self.hassolution:
                # print("=======================================")
                # print("AFTER PROCESSED:")
                # print(self.network)
                # print("================ ")
                # print("self.trail before revert change: ")
                for i in self.trail.trailStack:
                    pass
                    # print("variable --> " + str(i[0]))
                    # print("domain backup --> " + str(i[1]))
                # print("================= ")

                self.trail.undo()
                self.numBacktracks += 1
                # print("REVERT CHANGES:")
                # print(self.network)
                # print("================ ")
                # print("self.trail after revert change: ")
                for i in self.trail.trailStack:
                    pass
                    # print("variable --> " + str(i[0]))
                    # print("domain backup --> " + str(i[1]))
                # print("================= ")

            else:
                return
