#include "dpll_solver.h"

vector<Variable> variables;
deque<Clause> clauses;  // uses deque instead of vector to avoid dangling pointers
vector<pair<Variable*, Mark>> assignments;
vector<Clause*> unit_clauses;
map<int, Variable*> pure_lits;
Heap unassigned_vars;
Heuristic heu = Heuristic::none;  // The default setting is without any heuristics.
bool verbose = false;

// Append a variable to the heap and re-sort the heap.
void Heap::insert(Variable* var) {
    heap.push_back(var);
    var->pos_in_heap = heap.size()-1;
    move_up(var);
}

// Remove a variable from the heap and re-sort the heap.
void Heap::remove(Variable* var) {
    Variable* end_var = heap[heap.size()-1];
    swap(heap[var->pos_in_heap], heap[heap.size()-1]);  // First swap the to-be-removed variable with the last variable.
    heap.pop_back();
    end_var->pos_in_heap = var->pos_in_heap;
    move_down(end_var);
}

// When a variable's priority is bigger than its parent's, it percolates up in the heap.
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

// When a variable's priority is smaller than its children's, it percolates down in the heap.
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

int get_or_default(const map<int,int>& m, int l) {
    auto search = m.find(l);
    if (search != m.end()) { return search->second; }
    return 0;
}

double mom_helper(Variable* v, int len, int alpha) {
    int pos_cl_count = get_or_default(v->pos_by_cl_len, len);
    int neg_cl_count = get_or_default(v->neg_by_cl_len, len);
    return (pos_cl_count + neg_cl_count) * pow(2, alpha) + pos_cl_count * neg_cl_count;
}

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
            return max(v1->pos_lit_occ, v1->neg_lit_occ) > max(v2->pos_lit_occ, v2->neg_lit_occ);
        case Heuristic::dlcs:
            // Compare variables according to their number of occurrences in active clauses.
            return v1->pos_lit_occ + v1->neg_lit_occ > v2->pos_lit_occ + v2->neg_lit_occ;
        case Heuristic::set_count:
            return v1->priority > v2->priority;
        case Heuristic::mom: {
            const int alpha = 50;
            int cl_len = numeric_limits<int>::max();
            if (v1->pos_by_cl_len.begin() != v1->pos_by_cl_len.end()) {
                cl_len = v1->pos_by_cl_len.begin()->first;
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
            const double alpha = 100;
            const double beta = 50;
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
                if (cl_len == std::numeric_limits<int>::max()) { return false; }
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
                v1_pos = it_incr(v1->pos_by_cl_len, v1_pos, cl_len);
                v1_neg = it_incr(v1->neg_by_cl_len, v1_neg, cl_len);
                v2_pos = it_incr(v2->pos_by_cl_len, v2_pos, cl_len);
                v2_neg = it_incr(v2->neg_by_cl_len, v2_neg, cl_len);
            }
        }
        case Heuristic::jw:{
            return jeroslow_wang(v1) > jeroslow_wang(v2);
        }
        default:
            // Compare variables according to their pointer values, which correponds to the numeric value of the variables in the input file.
            return v1 > v2;
    }
}

int jeroslow_wang(Variable* v){
    int i = 0;
    int j = 0;

    while(i < v->pos_lit_occ){
        for (auto cl: v->pos_occ){
            if(cl->sat_var==nullptr){
                j += pow(2, cl->active);
                ++i;
            }
        }
    }
    i = 0;
    while(i < v->neg_lit_occ){
        for (auto cl: v->neg_occ){
            if(cl->sat_var==nullptr){
                j += pow(2, cl->active);
                ++i;
            }
        }
    }
    return j; 
}
// Pick a polarity for a variable.
Value pick_polarity(Variable* v) {
    switch(heu) {
        case Heuristic::slis:
        case Heuristic::slcs:
            return (v->pos_occ.size() > v->neg_occ.size()) ? Value::t : Value::f;
        case Heuristic::dlis:
        case Heuristic::dlcs:
        case Heuristic::set_count:
        case Heuristic::mom:
        case Heuristic::boehm:
            return (v->pos_lit_occ > v->neg_lit_occ) ? Value::t : Value::f;
        default:
            return Value::t;
    }
}

bool is_wellformed(Variable* v) {
    int pos_sum = 0;
    int neg_sum = 0;
    for (pair<int,int> p: v->pos_by_cl_len) { pos_sum += p.second; }
    for (pair<int,int> p: v->neg_by_cl_len) { neg_sum += p.second; }
    return pos_sum == v->pos_lit_occ && neg_sum == v->neg_lit_occ;
}

// Assign truth value to a variable.
void Variable::set(Value new_value, Mark mark) {
    if (verbose) {
        cout << "set #" << (this - &*variables.begin()) << " to " << (new_value == Value::t) << "\n";
    }
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
                    // The variable's number of occurrences decreases by one, because the clause is satisfied, therefore deactivated.
                    int pure_contr = 1;
                    if (lit > 0){
                        if (var->pos_lit_occ > 0){
                            var->pos_lit_occ -=1;
                        }
                    } else {
                        if (var->neg_lit_occ > 0){
                            var->neg_lit_occ -=1;
                        }
                    }
                    //a^2+b^2 = (a+b)^2 <=> (a*b=0) && (a+b !=0)  <=> only one var = 0
                    if (pow(var->pos_lit_occ, 2) + pow(var->neg_lit_occ, 2) == pow(var->pos_lit_occ + var->neg_lit_occ, 2)){
                        pure_lits.insert(make_pair(var->var, var));
                    } else if (var->pos_lit_occ*var->neg_lit_occ == 0){
                        //if more than one claus are deleted by unit_prop in one branching
                        pure_lits.erase(var->var);
                    } 

                    map<int,int>& m = lit > 0 ? var->pos_by_cl_len : var->neg_by_cl_len;
                    auto search = m.find(cl->active);
                    if (search->second != 1) { search->second -= 1; }
                    else { m.erase(search); }
                    
                    // Since the variable's number of occurrences decreased, the priority can only decrease.
                    unassigned_vars.move_down(var);
                    assert(is_wellformed(var));
                }
            }
        }
    }
    for (Clause* cl: (value == Value::t) ? neg_occ : pos_occ) {
        if (cl->sat_var == nullptr) {
            cl->active -= 1;
            for (int lit: cl->lits) {
                Variable* var = &variables[abs(lit)];
                if (var->value == Value::unset) {
                    map<int,int>& m = lit > 0 ? var->pos_by_cl_len : var->neg_by_cl_len;
                    auto search = m.find(cl->active+1);
                    if (search->second != 1) { search->second -= 1; }
                    else { m.erase(search); }
                    m[cl->active] += 1;

                    // The number of clauses with fewer variables increase. Since our heuristics favor clauses of shorter length, the priority of the variable increases.
                    unassigned_vars.move_up(var);
                    assert(is_wellformed(var));
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
    if (verbose) cout << "unset #" << (this - &*variables.begin()) <<  "\n";
    for (Clause* cl: (value == Value::t) ? pos_occ : neg_occ) {
        if (cl->sat_var == this) {
            cl->sat_var = nullptr;
            for (int lit: cl->lits) {
                Variable* var = &variables[abs(lit)];
                if (var->value == Value::unset) {
                    // The variable's number of occurrences increases by one, because the variable that satistifed the clause is unset, therefore the clause is active again.
                    (lit > 0 ? var->pos_lit_occ : var->neg_lit_occ) += 1;
                    
                    (lit > 0 ? var->pos_by_cl_len : var->neg_by_cl_len)[cl->active] += 1;

                    // Since the variable's number of occurrences increased, the priority can only increase.
                    unassigned_vars.move_up(var);
                    assert(is_wellformed(var));
                }
            }
        }
    }
    for (Clause* cl: (value == Value::t) ? neg_occ : pos_occ) {
        if (cl->sat_var == nullptr) {
            cl->active += 1;
            for (int lit: cl->lits) {
                Variable* var = &variables[abs(lit)];
                if (var->value == Value::unset) {
                    map<int,int>& m = lit > 0 ? var->pos_by_cl_len : var->neg_by_cl_len;
                    auto search = m.find(cl->active-1);
                    if (search->second != 1) { search->second -= 1; }
                    else { m.erase(search); }
                    m[cl->active] += 1;

                    // The number of clauses with more variables increase. Since our heuristics favor clauses of shorter length, the priority of the variable decreases.
                    unassigned_vars.move_down(var);
                    assert(is_wellformed(var));
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
        variables.push_back(Variable(0));  // to allow indexing of variables to start from 1
        for (int i = 1; i < num_vars+1; ++i) {
            variables.push_back(Variable(i));
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
                    variables[lit].pos_lit_occ += 1;
                    variables[lit].pos_by_cl_len[cl->active] += 1;
                } else {
                    variables[-lit].neg_occ.push_back(cl);
                    variables[-lit].neg_lit_occ += 1;
                    variables[-lit].neg_by_cl_len[cl->active] += 1;
                }
            }
        }

        for (int i = 1; i < num_vars+1; ++i) {
            if (variables[i].pos_occ.empty() || variables[i].neg_occ.empty()){
                pure_lits.insert(make_pair(i, &variables[i]));
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

//pure literals and subsumption
void pure_Lit(){
    for (auto &paire :pure_lits){
        Variable* var = paire.second;
        if (var->value == Value::unset){
            Value v = Value::t;
            if(var->pos_occ.empty()){
                v = Value::f;
            }
            var->set(v, Mark::forced);
        }
    }
    pure_lits.clear();
}

void subs(){

}

// Backtracking
void backtrack() {
    unit_clauses.clear();
    pure_lits.clear();
    while (!assignments.empty()) {
        Variable* var = assignments.back().first;
        Mark mark = assignments.back().second;
        assignments.pop_back();
        ++var->priority;
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
    if (argc <= 1){
        cout<< "Please give at least the path to a cnf file \n";
        cout<< "and select one heuristics optionally with [-slis, -slcs, -dlis, -dlcs, -sc, -mom, -boehm]"<<endl;
        exit(0);
    } 
    for (int i = 1; i < argc; ++i) {
        string option = string(argv[i]);
        
        if (option[0] == '-') {
            if (option == "-slis") { heu = Heuristic::slis; }
            else if (option == "-slcs") { heu = Heuristic::slcs; }
            else if (option == "-dlis") { heu = Heuristic::dlis; }
            else if (option == "-dlcs") { heu = Heuristic::dlcs; }
            else if (option == "-sc") { heu = Heuristic::set_count; }
            else if (option == "-mom") { heu = Heuristic::mom; }
            else if (option == "-boehm") { heu = Heuristic::boehm; }
            else if (option == "-jw") { heu = Heuristic::jw; }
            else if (option == "-v") { verbose = true; }
            else {
                cout << "Unknown argument.\nPossible options:\n";
                cout << "-slis\tuse the S(tatic)LIS heuristic\n";
                cout << "-slcs\tuse the S(tatic)LCS heuristic\n";
                cout << "-dlis\tuse the DLIS heuristic\n";
                cout << "-dlcs\tuse the DLCS heuristic\n";
                cout << "-sc\tuse heuristic based on how many times a variable has been assigned a value\n";
                cout << "-mom\tuse the MOM heuristic\n";
                cout << "-boehm\tuse Boehm's heuristic\n";
                cout << "-jw\tuse the Jeroslaw-Wang heuristic\n";
                cout << "-v\tverbose mode for debugging\n";
                exit(1);
            }
        } else { filename = option; }
    }

    fromFile(filename);
    // Fill the unassigned_vars heap. Originally all variables are unassigned.
    for (int i = 1; i < variables.size(); ++i) { unassigned_vars.insert(&variables[i]); }
    // There could be unit clauses in the original formula. If unit-propagation solves the while formula, the following while-loop will not be executed.
    unit_prop();
    pure_Lit();

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
        pure_Lit();
    }
    cout << "s Satisfiable\n";
    cout << "v ";
    for (int i = 1; i < variables.size(); ++i) {
        cout << ((variables[i].value == Value::t) ? i : -i) << " ";
    }
    cout << "0\n";
    return 0;
}
