#include "dpll_solver.h"

vector<Variable> variables;
deque<Clause> clauses;  // uses deque instead of vector to avoid dangling pointers
vector<pair<Variable*, Mark>> assignments;
vector<Clause*> unit_clauses;
bool use_pure_lit = false;
vector<Variable*> pure_lits;
Heap unassigned_vars;
Heuristic heu = Heuristic::none;  // The default setting is without any heuristics.
bool update_active_occ = false;  // only update active occurrences when needed
bool verbose = false;

// Append a variable to the heap and re-sort the heap.
void Heap::insert(Variable* var) {
    heap.push_back(var);
    var->heap_position = heap.size()-1;
    move_up(var);
}

// Remove a variable from the heap and re-sort the heap.
void Heap::remove(Variable* var) {
    Variable* end_var = heap[heap.size()-1];
    swap(heap[var->heap_position], heap[heap.size()-1]);  // First swap the to-be-removed variable with the last variable.
    heap.pop_back();
    end_var->heap_position = var->heap_position;
    move_down(end_var);
}

// When a variable's priority is bigger than its parent's, it percolates up in the heap.
void Heap::move_up(Variable* var) {
    int var_ind = var->heap_position;
    while (var_ind > 1) {
        Variable* parent = heap[parent_ind(var_ind)];
        if (greater_than(var, parent)) {
            swap(heap[var_ind], heap[parent_ind(var_ind)]);
            parent->heap_position = var_ind;
            var_ind = parent_ind(var_ind);
        } else { break; }
    }
    var->heap_position = var_ind;
}

// When a variable's priority is smaller than its children's, it percolates down in the heap.
void Heap::move_down(Variable* var) {
    int var_ind = var->heap_position;
    while (true) {
        int max_child_ind = this->max_child_ind(var_ind);
        if (var_ind == max_child_ind || greater_than(heap[var_ind], heap[max_child_ind])) { break; }
        else {
            swap(heap[var_ind], heap[max_child_ind]);
            heap[var_ind]->heap_position = var_ind;
            var_ind = max_child_ind;
        }
    }
    heap[var_ind]->heap_position = var_ind;
}

// Return the number of occurrences (search->second) if the clause length (key of m) is found, otherwise return 0.
int get_or_default(const map<int,int>& m, int l) {
    auto search = m.find(l);
    if (search != m.end()) { return search->second; }
    return 0;
}

// Compute the mom-heuristic score for variable v.
double mom_helper(Variable* v, int len, int alpha) {
    int pos_cl_count = get_or_default(v->pos_by_cl_len, len);
    int neg_cl_count = get_or_default(v->neg_by_cl_len, len);
    return (pos_cl_count + neg_cl_count) * pow(2, alpha) + pos_cl_count * neg_cl_count;
}

// Increment the iterator if it points to the clause length l.
map<int,int>::iterator it_incr(const map<int,int>& m, map<int,int>::iterator it, int l) {
    if (it != m.end() && it->first == l) { return ++it; }
    return it;
}

// Different ways to compare priorities of literals/variables.
bool greater_than(Variable* v1, Variable* v2) {
    switch(heu) {
        case Heuristic::slis:
            // Static Literal Individual Sum: Compare literals according to their number of occurrences. It does not keep track of the change of clauses, therefore the priority value of each literal is not modified anymore once the heap is established.
            return max(v1->pos_occ.size(), v1->neg_occ.size()) > max(v2->pos_occ.size(), v2->neg_occ.size());
        case Heuristic::slcs:
            // Static Literal Combined Sum: Compare variables according to their number of occurrences (both as positive and negative literals).
            return v1->pos_occ.size() + v1->neg_occ.size() > v2->pos_occ.size() + v2->neg_occ.size();
        case Heuristic::dlis:
            // Compare literals according to their number of occurrences in active clauses.
            return max(v1->active_pos_occ, v1->active_neg_occ) > max(v2->active_pos_occ, v2->active_neg_occ);
        case Heuristic::dlcs:
            // Compare variables according to their number of occurrences in active clauses.
            return v1->active_pos_occ + v1->active_neg_occ > v2->active_pos_occ + v2->active_neg_occ;
        case Heuristic::backtrack_count:
            // Compare variables according to how many times they have been backtracked.
            return v1->backtrack_count > v2->backtrack_count;
        case Heuristic::mom: {
            // Compare variables according to their mom-heuristic scores regarding the minimal clause length.
            const int alpha = 50;
            
            // Among all the active clauses that contain at least one of v1 and v2, find the length of the shortest clause.
            int cl_len = numeric_limits<int>::max();
            if (v1->pos_by_cl_len.begin() != v1->pos_by_cl_len.end()) {  // check if the map is empty
                cl_len = min(cl_len, v1->pos_by_cl_len.begin()->first);
            }
            if (v1->neg_by_cl_len.begin() != v1->neg_by_cl_len.end()) {
                cl_len = min(cl_len, v1->neg_by_cl_len.begin()->first);
            }
            if (v2->pos_by_cl_len.begin() != v2->pos_by_cl_len.end()) {
                cl_len = min(cl_len, v2->pos_by_cl_len.begin()->first);
            }
            if (v2->neg_by_cl_len.begin() != v2->neg_by_cl_len.end()) {
                cl_len = min(cl_len, v2->neg_by_cl_len.begin()->first);
            }

            double v1_heu = mom_helper(v1, cl_len, alpha);
            double v2_heu = mom_helper(v2, cl_len, alpha);
            return v1_heu > v2_heu;
        }
        case Heuristic::boehm: {
            // Compare variables according to their boehm-heuristic scores lexicographically.
            const int alpha = 100;
            const int beta = 50;

            // Among all the active clauses that contain at least one of v1 and v2, find the length of the shortest clause. Increase the length until the boehm-heuristic scores of v1 and v2 are different.
            auto v1_pos = v1->pos_by_cl_len.begin();
            auto v1_neg = v1->neg_by_cl_len.begin();
            auto v2_pos = v2->pos_by_cl_len.begin();
            auto v2_neg = v2->neg_by_cl_len.begin();
            while (true) {
                int cl_len = numeric_limits<int>::max();
                if (v1_pos != v1->pos_by_cl_len.end()) {
                    cl_len = v1_pos->first;
                }
                if (v1_neg != v1->neg_by_cl_len.end()) {
                    cl_len = min(cl_len, v1_neg->first);
                }
                if (v2_pos != v2->pos_by_cl_len.end()) {
                    cl_len = min(cl_len, v2_pos->first);
                }
                if (v2_neg != v2->neg_by_cl_len.end()) {
                    cl_len = min(cl_len, v2_neg->first);
                }
                
                // If the heuristic scores of v1 and v2 regarding all the occurring clause lengths are the same, return false.
                if (cl_len == numeric_limits<int>::max()) { return false; }

                // Compute the boehm-heuristic scores.
                int v1_pos_count = get_or_default(v1->pos_by_cl_len, cl_len);
                int v1_neg_count = get_or_default(v1->neg_by_cl_len, cl_len);
                int v2_pos_count = get_or_default(v2->pos_by_cl_len, cl_len);
                int v2_neg_count = get_or_default(v2->neg_by_cl_len, cl_len);
                int v1_max = max(v1_pos_count, v1_neg_count);
                int v1_min = min(v1_pos_count, v1_neg_count);
                int v2_max = max(v2_pos_count, v2_neg_count);
                int v2_min = min(v2_pos_count, v2_neg_count);
                double v1_heu = alpha * v1_max + beta * v1_min;
                double v2_heu = alpha * v2_max + beta * v2_min;
                if (v1_heu != v2_heu) { return v1_heu > v2_heu; };

                // Increment the iterators that point to cl_len.
                v1_pos = it_incr(v1->pos_by_cl_len, v1_pos, cl_len);
                v1_neg = it_incr(v1->neg_by_cl_len, v1_neg, cl_len);
                v2_pos = it_incr(v2->pos_by_cl_len, v2_pos, cl_len);
                v2_neg = it_incr(v2->neg_by_cl_len, v2_neg, cl_len);
            }
        }
        case Heuristic::jw:
            // Compare literals according to their Jeroslow-Wang heuristic scores
            return max(v1->jw_pos, v1->jw_neg) > max(v2->jw_pos, v2->jw_neg);
        case Heuristic::none:
            // Pick a variable randomly
            return rand() % 2 == 0;
    }
}

// Pick a polarity for a variable.
Value pick_polarity(Variable* v) {
    switch(heu) {
        case Heuristic::slis:
        case Heuristic::slcs:
            return (v->pos_occ.size() > v->neg_occ.size()) ? Value::t : Value::f;
        case Heuristic::dlis:
        case Heuristic::dlcs:
        case Heuristic::backtrack_count:
        case Heuristic::mom:
        case Heuristic::boehm:
            return (v->active_pos_occ > v->active_neg_occ) ? Value::t : Value::f;
        case Heuristic::jw:
            return (v->jw_pos > v->jw_neg) ? Value::t : Value::f;
        case Heuristic::none:
            return rand()%2 == 0 ? Value::t : Value::f;
    }
}

// For assertion: Check if the number of occurrences in pos_by_cl_len and pos_by_cl_len are correct.
bool is_wellformed(Variable* v) {
    int pos_sum = 0;
    int neg_sum = 0;
    for (pair<int,int> p: v->pos_by_cl_len) { pos_sum += p.second; }
    for (pair<int,int> p: v->neg_by_cl_len) { neg_sum += p.second; }
    return pos_sum == v->active_pos_occ && neg_sum == v->active_neg_occ;
}

// Assign truth value to a variable.
void Variable::set(Value new_value, Mark mark) {
    if (verbose) {
        cout << "set #" << (this - &variables[0]) << " to " << (new_value == Value::t) << "\n";
    }
    assignments.push_back(make_pair(this, mark));
    value = new_value;
    unassigned_vars.remove(this);
    bool found_conflict = false;
    for (Clause* cl: (value == Value::t) ? pos_occ : neg_occ) {
        if (cl->sat_var == nullptr) {
            cl->sat_var = this;
            if (heu == Heuristic::jw) {
                // Since the clause is now satisfied, the occurrences of all the unassigned literals in the clause should no longer be counted towards the Jeroslow-Wang heuristic score. 
                for (int lit: cl->lits) {
                    Variable* var = &variables[abs(lit)];
                    if (var->value == Value::unset) { 
                        (lit > 0 ? var->jw_pos : var->jw_neg) -= pow(2, -cl->active);
                        unassigned_vars.move_down(var);
                    }
                }
            }
            if (update_active_occ) {
                for (int lit: cl->lits) {
                    Variable* var = &variables[abs(lit)];
                    if (var->value == Value::unset) {
                        // The literal's number of occurrences decreases by one, because the clause is satisfied, therefore deactivated.
                        // Every variable will be appended to pure_lits at most twice.
                        if (lit > 0) {
                            var->active_pos_occ -= 1;
                            if (use_pure_lit) {
                                if (var->active_pos_occ == 0) { pure_lits.push_back(var); }
                            }
                        } else {
                            var->active_neg_occ -= 1;
                            if (use_pure_lit) {
                                if (var->active_neg_occ == 0) { pure_lits.push_back(var); }
                            }
                        }
                        assert(active_pos_occ >= 0 && active_neg_occ >= 0);

                        // Decrement the number of clauses of length cl->active, because the clause is satisfied. Delete the pair from the map if the literal does not appear in clauses of this length anymore.
                        if (heu == Heuristic::mom || heu == Heuristic::boehm) {
                            map<int,int>& m = lit > 0 ? var->pos_by_cl_len : var->neg_by_cl_len;
                            auto search = m.find(cl->active);
                            if (search->second != 1) { search->second -= 1; }
                            else { m.erase(search); }
                            assert(is_wellformed(var));
                        }
                        // Since the variable's number of occurrences decreased, the priority can only decrease.
                        unassigned_vars.move_down(var);
                    }
                }
            }
        }
    }
    for (Clause* cl: (value == Value::t) ? neg_occ : pos_occ) {
        if (cl->sat_var == nullptr) {
            cl->active -= 1;
            if (heu == Heuristic::mom || heu == Heuristic::boehm || heu == Heuristic::jw) {
                for (int lit: cl->lits) {
                    Variable* var = &variables[abs(lit)];
                    if (var->value == Value::unset) {
                        if (heu == Heuristic::jw) {
                            // The literal now occurs in a shorter clause, therefore add the difference to the Jeroslow-Wang heuristic score.
                            (lit > 0 ? var->jw_pos : var->jw_neg) += pow(2, -(cl->active+1));
                        } else {
                        // The variable var is now in a clause with one fewer active literals, update the counts accordingly.  
                        map<int,int>& m = lit > 0 ? var->pos_by_cl_len : var->neg_by_cl_len;
                        auto search = m.find(cl->active+1);
                        if (search->second != 1) { search->second -= 1; }
                        else { m.erase(search); }
                        m[cl->active] += 1;
                        }
                        // The number of clauses with fewer variables increase. Since our heuristics favor clauses of shorter length, the priority of the variable increases.
                        unassigned_vars.move_up(var);
                        assert(is_wellformed(var));
                    }
                }
            }
            if (cl->active == 1) { unit_clauses.push_back(cl); } 
            else if (cl->active == 0) { found_conflict = true; }
        }
    }
    if (found_conflict) {backtrack();}
}

// Unassign truth value of a variable.
void Variable::unset() {
    if (verbose) cout << "unset #" << (this - &variables[0]) <<  "\n";
    for (Clause* cl: (value == Value::t) ? pos_occ : neg_occ) {
        if (cl->sat_var == this) {
            cl->sat_var = nullptr;
            if (heu == Heuristic::jw) {
                // Since the clause is now reactivated, the occurrences of all the unassigned literals in the clause should again be counted towards the Jeroslow-Wang heuristic score. 
                for (int lit: cl->lits) {
                    Variable* var = &variables[abs(lit)];
                    if (var->value == Value::unset) {
                        (lit > 0 ? var->jw_pos : var->jw_neg) += pow(2, -cl->active);
                        unassigned_vars.move_up(var);
                    }
                }                 
            }
            if (update_active_occ) {
                for (int lit: cl->lits) {
                    Variable* var = &variables[abs(lit)];
                    if (var->value == Value::unset) {
                        // The variable's number of occurrences increases by one, because the variable that satistifed the clause is unset, therefore the clause is active again.
                        (lit > 0 ? var->active_pos_occ : var->active_neg_occ) += 1;

                        if (heu == Heuristic::mom || heu == Heuristic::boehm) {
                            (lit > 0 ? var->pos_by_cl_len : var->neg_by_cl_len)[cl->active] += 1;
                            assert(is_wellformed(var));
                        }

                        // Since the variable's number of occurrences increased, the priority can only increase.
                        unassigned_vars.move_up(var);
                    }
                }
            }
        }
    }
    for (Clause* cl: (value == Value::t) ? neg_occ : pos_occ) {
        if (cl->sat_var == nullptr) {
            cl->active += 1;
            if (heu == Heuristic::mom || heu == Heuristic::boehm || heu == Heuristic::jw) {
                for (int lit: cl->lits) {
                    Variable* var = &variables[abs(lit)];
                    if (var->value == Value::unset) {
                        if (heu == Heuristic::jw) {
                            // The literal now occurs in a longer clause, therefore subtract the difference from the Jeroslow-Wang heuristic score.
                            (lit > 0 ? var->jw_pos : var->jw_neg) -= pow(2, -cl->active);
                        } else {
                            // The variable var is now in a clause with one more active literal, update the counts accordingly.                    
                            map<int,int>& m = lit > 0 ? var->pos_by_cl_len : var->neg_by_cl_len;
                            auto search = m.find(cl->active-1);
                            if (search->second != 1) { search->second -= 1; }
                            else { m.erase(search); }
                            m[cl->active] += 1;
                        }
                        // The number of clauses with more variables increase. Since our heuristics favor clauses of shorter length, the priority of the variable decreases.
                        unassigned_vars.move_down(var);
                        assert(is_wellformed(var));
                    }
                }
            }
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
            set<int> lits_set;  // removes duplicate literals; for detecting tautological clause
            int lit;
            file >> lit;
            while (lit != 0) {
                lits_set.insert(lit);
                file >> lit;
            }
            
            // Only process non-tautological clauses.
            bool tautology = false;
            for (int lit: lits_set) {
                if (lits_set.count(-lit) > 0) {
                    tautology = true;
                    break;
                }
            }
            if (tautology) { continue; }
            vector<int> lits;
            for (int lit: lits_set) { lits.push_back(lit); }
            clauses.push_back(Clause(lits, lits.size()));

            Clause* cl = &clauses.back();
            if (cl->active == 1) { unit_clauses.push_back(cl); }

            for (int lit: lits) {
                if (lit > 0) {
                    variables[lit].pos_occ.push_back(cl);
                    variables[lit].active_pos_occ += 1;
                    variables[lit].pos_by_cl_len[cl->active] += 1;
                    variables[lit].jw_pos += pow(2, -cl->active);
                } else {
                    variables[-lit].neg_occ.push_back(cl);
                    variables[-lit].active_neg_occ += 1;
                    variables[-lit].neg_by_cl_len[cl->active] += 1;
                    variables[-lit].jw_neg += pow(2, -cl->active);
                }
            }
        }

        for (int i = 1; i < num_vars+1; ++i) {
            if (variables[i].pos_occ.empty() || variables[i].neg_occ.empty()){
                pure_lits.push_back(&variables[i]);
            }
        }
        assert(variables.size() == num_vars+1);
    }
}

// Unit propagation
void unit_prop() {
    while (!unit_clauses.empty()) {
        Clause* cl = unit_clauses.back();
        unit_clauses.pop_back();
        for (int lit: cl->lits) {
            Variable* var = &variables[abs(lit)];
            if (var->value == Value::unset) {  // A clause does not keep track of which literals are unassigned.
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

// Pure literal elimination
void pure_lit(){
    if (use_pure_lit) {
        for (Variable* var: pure_lits){
            if (var->value == Value::unset){
                Value v = var->active_pos_occ == 0 ? Value::f : Value::t;
                var->set(v, Mark::forced);
            }
        }
        pure_lits.clear();
    }
}

// Backtracking
void backtrack() {
    unit_clauses.clear();
    pure_lits.clear();
    while (!assignments.empty()) {
        Variable* var = assignments.back().first;
        Mark mark = assignments.back().second;
        assignments.pop_back();
        ++var->backtrack_count;  // The priority of a variable increases if it is on the backtracking path.
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
    cout << "s UNSATISFIABLE\n";
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
            else if (option == "-bc") { heu = Heuristic::backtrack_count; }
            else if (option == "-mom") { heu = Heuristic::mom; }
            else if (option == "-boehm") { heu = Heuristic::boehm; }
            else if (option == "-jw") { heu = Heuristic::jw; }
            else if (option == "-p") { use_pure_lit = true; }
            else if (option == "-v") { verbose = true; }
            else {
                cout << "Unknown argument: " << option << "\nPossible options:\n";
                cout << "-slis\tuse the S(tatic)LIS heuristic\n";
                cout << "-slcs\tuse the S(tatic)LCS heuristic\n";
                cout << "-dlis\tuse the DLIS heuristic\n";
                cout << "-dlcs\tuse the DLCS heuristic\n";
                cout << "-bc\tbacktrack count: a heuristic based on how many times a variable has been backtracked\n";
                cout << "-mom\tuse the MOM heuristic\n";
                cout << "-boehm\tuse Boehm's heuristic\n";
                cout << "-jw\tuse the Jeroslow-Wang heuristic\n";
                cout << "-p\tenable pure literal elimination\n";
                cout << "-v\tverbose mode for debugging\n";
                exit(1);
            }
        } else { filename = option; }
    }
    // When no file name is given.
    if (filename == "") {
        cout << "No filename specified\n";
        cout << "usage: dpll_solver <path to a cnf file> [-p] [heuristics]\n";
        exit(1);
    }

    if (heu == Heuristic::dlis || heu == Heuristic::dlcs || heu == Heuristic::mom || heu == Heuristic::boehm || use_pure_lit) { update_active_occ = true; }

    fromFile(filename);
    // Fill the unassigned_vars heap. Originally all variables are unassigned.
    for (int i = 1; i < variables.size(); ++i) { unassigned_vars.insert(&variables[i]); }
    // There could be unit clauses in the original formula. If unit-propagation and pure literal elimination solve the whole formula, the following while-loop will not be executed.
    unit_prop();
    pure_lit();

    while (variables.size()-1 != assignments.size()) {
        // Always pick the variable of highest priority to branch on.
        Variable* picked_var = unassigned_vars.heap[1];
        if (verbose) {
            cout << "branching on #" << (picked_var - &*variables.begin()) << " pos_occ: ";
            for (pair<int,int> p : picked_var->pos_by_cl_len) {
                cout << p.first << ":" << p.second << " ";
            }
            cout << " neg_occ: ";
            for (pair<int,int> p : picked_var->neg_by_cl_len) {
                cout << p.first << ":" << p.second << " ";
            }
            cout << "\n";
        }
        picked_var->set(pick_polarity(picked_var), Mark::branching);
        unit_prop();
        pure_lit();
    }
    cout << "s SATISFIABLE\n";
    cout << "v ";
    for (int i = 1; i < variables.size(); ++i) {
        cout << ((variables[i].value == Value::t) ? i : -i) << " ";
    }
    cout << "0\n";
    return 0;
}
