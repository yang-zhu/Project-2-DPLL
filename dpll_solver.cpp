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

struct Variable {
    Value value = Value::unset;
    vector<Clause*> pos_occ;
    vector<Clause*> neg_occ;
    void set(Value);
    void unset();
};

vector<Variable> variables;
deque<Clause> clauses;  // Use deque instead of vector to avoid dangling pointers
vector<pair<Variable*, char>> assignments;
vector<Clause*> unit_queue;

void backtrack();

// Assign truth value to a variable.
void Variable::set(Value value) {
    this->value = value;
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
                unit_queue.push_back(cl);
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
    this->value = Value::unset;
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
        variables.push_back(Variable());
        for (int i = 1; i < num_vars+1; ++i) {
            variables.push_back(Variable());
        }

        // Fill the deque of clauses.
        for (int i = 0; i < num_clauses; ++i) {
            vector<int> lits;
            int var;
            file >> var;
            while (var != 0) {
                lits.push_back(var);
                file >> var;
            }
            clauses.push_back(Clause(lits, lits.size()));
            Clause* cl = &clauses[i];
            
            if (cl->active == 1) {unit_queue.push_back(cl);}

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
    while (!unit_queue.empty()) {
        Clause* cl = unit_queue.back();
        unit_queue.pop_back();
        for (int lit: cl->lits) {
            Variable* var = &variables[abs(lit)];
            if (var->value == Value::unset) {
                if (lit > 0) {
                    assignments.push_back(make_pair(var, 'f'));
                    var->set(Value::t);
                } else {
                    assignments.push_back(make_pair(var, 'f'));
                    var->set(Value::f);
                }
                break;
            }
        }
    }
}

// Backtracking
void backtrack() {
    unit_queue.clear();
    while (!assignments.empty()) {
        Variable* var = assignments.back().first;
        char mark = assignments.back().second;
        assignments.pop_back();
        if (mark == 'f') {var->unset();}
        else {
            Value old_value = var->value;
            var->unset();
            assignments.push_back(make_pair(var, 'f'));
            var->set((old_value == Value::t) ? Value::f : Value::t);
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
        for (int i = 1; i < variables.size(); ++i) {
            Variable* var = &variables[i];
            if (var->value == Value::unset) {
                assignments.push_back(make_pair(var, 'b'));
                var->set(Value::t);
                unit_prop();
            }
        }
        if (variables.size()-1 == assignments.size()) {
            cout << "Satisfiable";
            return 0;
        }
    }
}