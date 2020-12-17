import sys

class Clause:
    def __init__(self, lits, num, sat_var=None):
        self.sat_var = sat_var
        self.lits = lits
        self.active = num
    
    def __repr__(self):
        return "∨".join(map(str, self.lits))

    def __str__(self):
        return "sat_var: " + str(self.sat_var) + "; literals: " + str(self.lits) + "; active: " + str(self.active)

class Variable:
    def __init__(self, id=None, value=None):
        self.id = id
        self.value = value
        self.pos_occ = []
        self.neg_occ = []
    
    def set(self, value):
        self.value = value
        found_conflict = False
        for cl in (self.pos_occ if value else self.neg_occ):
            if cl.sat_var == None:
                cl.sat_var = self.id
        for cl in (self.neg_occ if value else self.pos_occ):
            if cl.sat_var == None:
                cl.active -= 1
                if cl.active == 1:
                    unit_queue.append(cl)
                elif cl.active == 0:
                    found_conflict = True
        if found_conflict:
            backtrack()
    
    def unset(self):
        for cl in (self.pos_occ if self.value else self.neg_occ):
            if cl.sat_var == self.id:
                cl.sat_var = None
        for cl in (self.neg_occ if self.value else self.pos_occ):
            if cl.sat_var == None:
                cl.active += 1
        self.value = None
    
    def __repr__(self):
        return "#"+str(self.id)+'='+str(self.value)

    def __str__(self):
        return "var: " + str(self.id) + "; value: " + str(self.value) + "; pos_occ: " + str(self.pos_occ) + "; neg_occ: " + str(self.neg_occ)

variables = [None]
clauses = []
assignments = []
unit_queue = []


def fromFile(path):
    with open(path) as f:
        lines = f.read().split('\n')
        for line in lines:
            if line == '':
                break
            lits_str = line.split()
            if lits_str[0] != 'c':
                if lits_str[0] == 'p':
                    numVars = int(lits_str[-2])
                    for var in range(1, numVars+1):
                        variables.append(Variable(id=var))
                    numClauses = int(lits_str[-1])
                else:
                    lits = list(map(int, lits_str))[:-1]
                    cl = Clause(lits, len(lits))
                    if len(lits) == 1:
                        unit_queue.append(cl)
                    clauses.append(cl)
                    for var in lits:
                        if var > 0:
                            variables[var].pos_occ.append(cl)
                        else:
                            variables[-var].neg_occ.append(cl)
    assert len(variables) == numVars+1 and len(clauses) == numClauses


def unit_prop():
    while unit_queue != []:
        cl = unit_queue.pop()
        for lit in cl.lits:
            var = variables[abs(lit)]
            if var.value == None:
                if lit > 0:
                    assignments.append((var, 'f'))
                    var.set(True)
                else:
                    assignments.append((var, 'f'))
                    var.set(False)
                break
                    

def backtrack():
    unit_queue.clear()
    while assignments != []:
        (var, mark) = assignments.pop()
        if mark == 'f':
            var.unset()
        else: 
            old_value = var.value
            var.unset()
            assignments.append((var, 'f'))
            var.set(not old_value)            
            return
    print("Unsatisfiable")
    exit()


fromFile(sys.argv[1])
unit_prop()
while True:
    for var in variables:
        if var != None:
            if var.value == None:
                assignments.append((var, 'b'))
                var.set(True)
                unit_prop()
    if len(variables) - 1 == len(assignments):
        print("Satisfiable")
        exit()