CLAUSE_LIST = [(1,), (0,)]
N = 3
A = 65


class SAT:
    """
    This class is an SAT solver. Create an instance by passing in a list of clauses and the number of variables

    Uses notation of 2N + 1 to input tuples of clauses

    Ex: (A+B)(~B+C) - > (0, 2)(3, 4)

    There are 3 variables so:
    A = 0 = 2*(0)
    ~A = 1 = 2*(0) + 1

    B = 2 = 2*(1)
    ~B = 3 = 2*(1) + 1

    C = 4 = 2*(3)
    ~C = 5 = 2*(1) + 1

    """

    def __init__(self, clauseList, numOfVar):
        self.clauseList = clauseList
        self.numOfVar = numOfVar

        self.vars = {}

        self.solutions = {}
        self.masterSolutionSet = []
        self.final = []

        self.makeDict()
        self.makeSolutions()

        self.neg = False

    def makeSolutions(self):
        for key in self.vars.keys():
            self.solutions[key] = []

    def makeDict(self):
        """
        Will auto gen a dict containing all variables in it as a look-up reference
        Sets val of each key/val pair to None

        True=1
        False=0
        None=Variable has not been set yet

        For example:

        (0, 2)(3, 4) will return a dict of

        {
        "X0": None,
        "X1": None,
        "X2": None
        }

        :return:
        """
        i = 0
        while i < self.numOfVar:
            temp = {"X{}".format(i): None}
            self.vars.update(temp)
            i += 1

    def getBool(self, val, vars):
        """
        Returns the value of each variable in a clause
        Will return True, False, or None based on current var values

        Example:

        The current set variables (vars) is:
        {
        "X0": True,
        "X1": None,
        "X2": None
        }

        For these given val inputs here are the expect outputs:

        Input: 0 -> Output: True
        Input: 1 -> Output: False

        Input: 2 -> Output: None
        Input: 3 -> Output: None

        Input: 4 -> Output: None
        Input: 5 -> Output: None

        :param val:
        :param vars:
        :return:
        """

        key, isNot = self.getKeyForBool(val=val)

        boolVal = vars.get(key)

        if boolVal is None:
            return boolVal

        if isNot:
            boolVal = not boolVal

        return boolVal

    def getKeyForBool(self, val):
        isNot = False
        if (val % 2) != 0:
            isNot = True
            val - 1

        n = val // 2
        key = "X{}".format(n)

        return key, isNot

    def testClause(self, pair, vars):
        """
        Input a pair - i.e. a single clause (of type=tuple)
        Will determine if that clause is True, False, or None

        True=contains a 1 thus the 'or'ing will evaluate clause to 1
        False=contains no 1's and all variables in clause are not None
        None=more branching is needed

        Example:

        Given inputs of ...

        vars = {
        "X0": True,
        "X1": None,
        "X2": None
        }

        pair = (0, 2)

        Then ...

        boolList = (True, None)

        return True

        .....

        Given inputs of ...

        vars = {
        "X0": True,
        "X1": None,
        "X2": None
        }

        pair = (3, 4)

        Then ...

        boolList = (None, None)

        return None


        :param pair:
        :param vars:
        :return:
        """

        boolList = self.getBoolList(pair=pair, vars=vars)

        if True in boolList:
            return True

        if None in boolList:
            return

        else:
            return False

    def getBoolList(self, pair, vars):
        tempList = []

        for item in pair:
            tempList.append(self.getBool(val=item, vars=vars))

        return tempList

    def checkClauses(self, vars, clauses):
        """
        Takes in a list of clauses to operate on and check their 'truth-y-ness'
        Returns a list of evaluations



        :param vars:
        :param clauses:
        :return:
        """
        results = []

        for clause in clauses:
            results.append(self.testClause(pair=clause, vars=vars))

        return results

    def preBranch(self, clauses, vars):
        """
        This will check what is going on with the current branch operation

        It takes a list of clauses and the dict of current vars

        Will determine what, if any, clauses have been satisfied and add variables to the results list
        If a clause has been satisfied it will be removed from the list of clauses for the next branch as we have already solved it

        Example:

        Given Inputs of ...

        clauses = [(0, 2), (2, 5)]
        vars = {
        "X0": True,
        "X1": None,
        "X2": None
        }

        Then ...

        results = [True, None]

        Will return ...

        tempClauses = [(2,5)]
        tempVar = ["X0=1"]


        :param clauses:
        :param vars:
        :return:
        """
        tempClauses = clauses.copy()
        tempVar = []
        results = self.checkClauses(vars=vars, clauses=clauses)

        for result, val in zip(results, clauses):
            if result:
                varVals = self.getVarValues(vars=vars, val=val)
                boolList = self.getBoolList(vars=vars, pair=val)

                while None in boolList:
                    boolList.remove(None)

                for solution, status in zip(varVals, boolList):
                    if status:
                        temp = solution.split("=")[0]
                        kelVal = vars.get(temp)

                        if kelVal:
                            newResult = f"{temp}=1"
                            tempVar.append(newResult)
                        else:
                            newResult = f"{temp}=0"
                            tempVar.append(newResult)

                tempClauses.remove(val)

            if result is False:
                return None, None

        return tempClauses, tempVar

    def getVarValues(self, vars, val):
        """
        Takes in a var that has been determined to solve a clause. Finds the values for the variables in the solved clause.
        Does not count variables of value None as an answer

        Example:

        Given inputs of ...
        vars = {
        "X0": True,
        "X1": None,
        "X2": None
        }

        val = (0,2)

        returns ...

        results = ["X0=1"]

        :param vars:
        :param val:
        :return:
        """

        results = []

        for item in val:
            value = self.getBool(vars=vars, val=item)

            if value is not None:
                key, isNot = self.getKeyForBool(val=item)

                if value:
                    toSave = 1
                else:
                    toSave = 0

                strToAdd = f"{key}={toSave}"
                results.append(strToAdd)

        return results

    def starter(self):
        vars = self.vars
        clauses = self.clauseList
        keyList = [*self.vars]

        self.tree(key=keyList[0], vars=vars, clauses=clauses, keyList=keyList)


        print("\n____Solution Set____")

        if self.final:
            for count, thing in enumerate(self.final):
                count += 1
                val = f"Solution {count}: "
                for item in thing:
                    val += f"{item}, "

                print(val[:-2])

        else:
            print("No solutions exist.")

    def formatSolutions(self):
        for key in self.solutions.keys():
            solutionList = self.solutions.get(key)

            for item in solutionList:
                self.masterSolutionSet.append(item)

    def tree(self, key, vars, clauses, keyList, solutionSet=None):
        keyListA = keyList.copy()
        keyListB = keyList.copy()
        keyCopyA = key
        keyCopyB = key

        if solutionSet is None:
            solutionSet = []

        self.posSolver(vars=vars, clauses=clauses, key=keyCopyA, keyList=keyListA, solutionSet=self.solutions)

        vars = self.varReset(vars=vars)

        for key in self.solutions:
            self.solutions[key] = []

        self.negSolver(vars=vars, clauses=clauses, key=keyCopyB, keyList=keyListB, solutionSet=self.solutions)

    def solutionReset(self):
        for item in self.masterSolutionSet:
            tempVal = item
            for key in item.keys():
                tempVal[key] = []

    def varReset(self, vars):
        for key in vars.keys():
            vars[key] = None

        return vars

    def posSolver(self, vars, clauses, key, keyList, solutionSet):
        vars[key] = True

        self.solver(vars=vars, clauses=clauses, key=key, keyList=keyList, solutionSet=solutionSet)

    def negSolver(self, vars, clauses, key, keyList, solutionSet):
        vars[key] = False

        self.solver(vars=vars, clauses=clauses, key=key, keyList=keyList, solutionSet=solutionSet)

    def solver(self, vars, clauses, key, keyList, solutionSet):
        reset = False
        for tempKey in vars.keys():
            if reset:
                vars[tempKey] = None
            if tempKey == key:
                reset = True

        remainingClauses, currentSolutionSet = run.preBranch(vars=vars, clauses=clauses)

        if remainingClauses is None:
            return

        if currentSolutionSet:
            if currentSolutionSet not in solutionSet.get(key):
                solutionSet[key].append(currentSolutionSet)

        if remainingClauses:
            keyList.remove(key)
            key = keyList[0]
            self.posSolver(key=key, vars=vars, clauses=remainingClauses.copy(), keyList=keyList, solutionSet={k: v.copy() for k, v in solutionSet.items()})
            self.negSolver(key=key, vars=vars, clauses=remainingClauses.copy(), keyList=keyList, solutionSet={k: v.copy() for k, v in solutionSet.items()})

        else:
            tempSolutions = []
            for key in solutionSet.keys():
                tempList = solutionSet.get(key)
                for solutionList in tempList:
                    for item in solutionList:
                        tempSolutions.append(item)

            if tempSolutions not in self.final and tempSolutions:
                self.final.append(tempSolutions)


if __name__ == '__main__':
    run = SAT(clauseList=CLAUSE_LIST, numOfVar=N)

    run.starter()
