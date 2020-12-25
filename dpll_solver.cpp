#include "dpll_solver.h"

vector<Variable> variables;
deque<Clause> clauses;  // uses deque instead of vector to avoid dangling pointers
vector<pair<Variable*, Mark>> assignments;
vector<Clause*> unit_clauses;
Heap unassigned_vars;

enum class Heuristic {
    none, slis, slcs, dlis, dlcs//, mom, boehm, jw
};

Heuristic heu {Heuristic::none};

void Heap::insert(Variable* var) {
    heap.push_back(var);
    var->pos_in_heap = heap.size()-1;
    move_up(var);
}

void Heap::remove(Variable* var) {
    Variable* end_var = heap[heap.size()-1];
    swap(heap[var->pos_in_heap], heap[heap.size()-1]);
    heap.pop_back();
    end_var->pos_in_heap = var->pos_in_heap;
    move_down(end_var);
}

void Heap::move_up(Variable* var) {
    int var_ind = var->pos_in_heap;
    while (var_ind > 1) {
        Variable* parent = heap[parent_ind(var_ind)];
        if (greater_than(var, parent)) { 
            swap(heap[var_ind], heap[parent_ind(var_ind)]);
            parent->pos_in_heap = var_ind;
            var_ind = parent_ind(var_ind);
        } else { break; }
    }
    var->pos_in_heap = var_ind;
}

void Heap::move_down(Variable* var) {
    int var_ind = var->pos_in_heap;
    while (true) {
        int max_child_ind = this->max_child_ind(var_ind);
        if (var_ind == max_child_ind || greater_than(heap[var_ind], heap[max_child_ind])) { break; }
        else {
            swap(heap[var_ind], heap[max_child_ind]);
            heap[var_ind]->pos_in_heap = var_ind;
            var_ind = max_child_ind;
        }
    }
    heap[var_ind]->pos_in_heap = var_ind;
}

// Compare variables according to their occurrences.
bool greater_than(Variable* v1, Variable* v2) {
    switch(heu) {
        case Heuristic::none:
            return v1 > v2;
        case Heuristic::slis:
            return max(v1->pos_occ.size(), v1->neg_occ.size()) > max(v2->pos_occ.size(), v2->neg_occ.size());
        case Heuristic::slcs:
            return v1->pos_occ.size() + v1->neg_occ.size() > v2->pos_occ.size() + v2->neg_occ.size();
        case Heuristic::dlis:
            return max(v1->pos_lit_occ, v1->neg_lit_occ) > max(v2->pos_lit_occ, v2->neg_lit_occ);
        case Heuristic::dlcs:
            return v1->pos_lit_occ + v1->neg_lit_occ > v2->pos_lit_occ + v2->neg_lit_occ;
    }    
}

// Pick a polarity for a variable.
Value pick_polarity(Variable* v) {
    switch(heu) {
        case Heuristic::none:
            return Value::t;
        case Heuristic::slis:
        case Heuristic::slcs:
            return (v->pos_occ.size() > v->neg_occ.size()) ? Value::t : Value::f;
        case Heuristic::dlis:
        case Heuristic::dlcs:
            return (v->pos_lit_occ > v->neg_lit_occ) ? Value::t : Value::f;
    }
}

// Assign truth value to a variable.
void Variable::set(Value new_value, Mark mark) {
    assignments.push_back(make_pair(this, mark));
    value = new_value;
    unassigned_vars.remove(this);
    bool found_conflict = false;
    for (Clause* cl: (value == Value::t) ? pos_occ : neg_occ) {
        if (cl->sat_var == nullptr) {
            cl->sat_var = this;
            for (int lit: cl->lits) {
                Variable* var = &variables[abs(lit)];
                if (var->value == Value::unset) {
                    (lit > 0 ? var->pos_lit_occ : var->neg_lit_occ) -= 1;
                    unassigned_vars.move_down(var); 
                }
            }
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
}

// Unassign truth value of a variable.
void Variable::unset() {
    for (Clause* cl: (value == Value::t) ? pos_occ : neg_occ) {
        if (cl->sat_var == this) {
            cl->sat_var = nullptr;
            for (int lit: cl->lits) {
                Variable* var = &variables[abs(lit)];
                if (var->value == Value::unset) {
                    (lit > 0 ? var->pos_lit_occ : var->neg_lit_occ) += 1;
                    unassigned_vars.move_up(var); 
                }
            }
        }
    }
    for (Clause* cl: (value == Value::t) ? neg_occ : pos_occ) {
        if (cl->sat_var == nullptr) {
            cl->active += 1;
        }
    }
    value = Value::unset;
    unassigned_vars.insert(this);
}

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
                    variables[lit].pos_lit_occ += 1;
                } else {
                    variables[-lit].neg_occ.push_back(cl);
                    variables[-lit].neg_lit_occ += 1;
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
        if (mark == Mark::forced) {
            var->unset();
        }
        else {
            Value old_value = var->value;
            var->unset();
            var->set((old_value == Value::t) ? Value::f : Value::t, Mark::forced);
            return;
        }
    }
    cout << "s Unsatisfiable\n";
    exit(0);
}

int main(int argc, const char* argv[]) {
    string filename;
    for (int i = 1; i < argc; ++i) {
        string option = string(argv[i]);
        if (option[0] == '-') {
            if (option == "-slis") { heu = Heuristic::slis; }
            else if (option == "-slcs") { heu = Heuristic::slcs; }
            else if (option == "-dlis") { heu = Heuristic::dlis; }
            else if (option == "-dlcs") { heu = Heuristic::dlcs; }
            // else if (option == "-mom") { heu = Heuristic::mom; }
            // else if (option == "-boehm") { heu = Heuristic::boehm; }
            // else if (option == "-jw") { heu = Heuristic::jw; }
            else { 
                cout << "Unknown argument.\nPossible options:\n";
                cout << "-slis\tuse the S(tatic)LIS heuristic\n";
                cout << "-slcs\tuse the S(tatic)LCS heuristic\n";
                cout << "-dlis\tuse the DLIS heuristic\n";
                cout << "-dlcs\tuse the DLCS heuristic\n";
                // cout << "-mom\tuse the MOM heuristic\n";
                // cout << "-boehm\tuse Boehm's heuristic\n";
                // cout << "-jw\tuse the Jeroslaw-Wang heuristic\n";
                exit(1); 
            }
        } else { filename = option; }
    }

    fromFile(filename);
    // Fills the unassigned_vars heap. Originally all variables are unassigned.
    for (int i = 1; i < variables.size(); ++i) { unassigned_vars.insert(&variables[i]); }
    // There could be unit clauses in the original formula.
    unit_prop();
    
    while (true) {
        Variable* picked_var = unassigned_vars.heap[1];
        picked_var->set(pick_polarity(picked_var), Mark::branching);
        unit_prop();

        if (variables.size()-1 == assignments.size()) {
            cout << "s Satisfiable\n";
            cout << "v ";
            for (int i = 1; i < variables.size(); ++i) {
                cout << ((variables[i].value == Value::t) ? i : -i) << " "; 
            }
            cout << "0\n";
            return 0;
        }
    }
}
