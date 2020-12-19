#include <iostream>
#include <fstream> 
#include <vector> 
#include <deque> 
#include <string>
#include <cassert>  

using namespace std;

struct Variable;

struct Clause {
    Variable* sat_var = nullptr;
    vector<int> lits;
    int active;

    Clause(vector<int> lits, int active) : lits{lits}, active{active} {}
};

// Represent truth value.
enum class Value {
    unset, f, t
};

// Distinguish between forced and branching literals.
enum class Mark {
    forced, branching
};

struct Variable {
    Value value = Value::unset;
    vector<Clause*> pos_occ;
    vector<Clause*> neg_occ;
    void set(Value, Mark);
    void unset();
};

vector<Variable> variables;
deque<Clause> clauses;  // uses deque instead of vector to avoid dangling pointers
vector<pair<Variable*, Mark>> assignments;
vector<Clause*> unit_clauses;

void backtrack();

// Assign truth value to a variable.
void Variable::set(Value new_value, Mark mark) {
    assignments.push_back(make_pair(this, mark));
    value = new_value;
    bool found_conflict = false;
    for (Clause* cl: (value == Value::t) ? pos_occ : neg_occ) {
        if (cl->sat_var == nullptr) {
            cl->sat_var = this;
        }
    }
    for (Clause* cl: (value == Value::t) ? neg_occ : pos_occ) {
        if (cl->sat_var == nullptr) {
            cl->active -= 1;
            if (cl->active == 1) {
                unit_clauses.push_back(cl);
            } else if (cl->active == 0) {
                found_conflict = true;
            }
        }
    }
    if (found_conflict) {backtrack();}
};

// Unassign truth value of a variable.
void Variable::unset() {
    for (Clause* cl: (value == Value::t) ? pos_occ : neg_occ) {
        if (cl->sat_var == this) {
            cl->sat_var = nullptr;
        }
    }
    for (Clause* cl: (value == Value::t) ? neg_occ : pos_occ) {
        if (cl->sat_var == nullptr) {
            cl->active += 1;
        }
    }
    value = Value::unset;
};

void fromFile(string path) {
    ifstream file = ifstream(path);
    string s;
    file >> s;
    
    // Read lines that start with "c" and ignore them.
    while (s == "c") {
        string line;
        getline(file, line);
        file >> s;
    }
    
    // Read the line that starts with "p" and get the number of variables as well as the number of clauses.
    if (s == "p") {
        string cnf;
        int num_vars;
        int num_clauses;
        file >> cnf >> num_vars >> num_clauses;
        
        // Fill the vector of variables.
        variables.push_back(Variable());  // to allow indexing of variables to start from 1
        for (int i = 1; i < num_vars+1; ++i) {
            variables.push_back(Variable());
        }

        // Fill the deque of clauses.
        for (int i = 0; i < num_clauses; ++i) {
            vector<int> lits;
            int lit;
            file >> lit;
            while (lit != 0) {
                lits.push_back(lit);
                file >> lit;
            }
            clauses.push_back(Clause(lits, lits.size()));

            Clause* cl = &clauses[i];
            if (cl->active == 1) {unit_clauses.push_back(cl);}

            for (int lit: lits) {
                if (lit > 0) { 
                    variables[lit].pos_occ.push_back(cl);
                } else {
                    variables[-lit].neg_occ.push_back(cl);
                }
            }
        }
        assert(variables.size() == num_vars+1);
        assert(clauses.size() == num_clauses);
    }
}

// Unit propagation
void unit_prop() {
    while (!unit_clauses.empty()) {
        Clause* cl = unit_clauses.back();
        unit_clauses.pop_back();
        for (int lit: cl->lits) {
            Variable* var = &variables[abs(lit)];
            if (var->value == Value::unset) {  // a clause does not keep track of which literals are unassigned
                if (lit > 0) {
                    var->set(Value::t, Mark::forced);
                } else {
                    var->set(Value::f, Mark::forced);
                }
                break;
            }
        }
    }
}

// Backtracking
void backtrack() {
    unit_clauses.clear();
    while (!assignments.empty()) {
        Variable* var = assignments.back().first;
        Mark mark = assignments.back().second;
        assignments.pop_back();
        if (mark == Mark::forced) {var->unset();}
        else {
            Value old_value = var->value;
            var->unset();
            var->set((old_value == Value::t) ? Value::f : Value::t, Mark::forced);
            return;
        }
    }
    cout << "Unsatisfiable";
    exit(0);
}

int main(int argc, const char *argv[]) {
    fromFile(argv[1]);
    unit_prop();
    while (true) {
        // We have to go through the variables many times, because set variables could be unset again by backtracking.
        for (int i = 1; i < variables.size(); ++i) {
            Variable* var = &variables[i];
            if (var->value == Value::unset) {
                var->set(Value::t, Mark::branching);
                unit_prop();
            }
        }
        if (variables.size()-1 == assignments.size()) {
            cout << "Satisfiable";
            return 0;
        }
    }
}