#ifndef DPLL_SOLVER_H
#define DPLL_SOLVER_H

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
    int pos_lit_occ = 0;
    int neg_lit_occ = 0;
    int pos_in_heap = 0;
    void set(Value, Mark);
    void unset();
};

bool greater_than(Variable*, Variable*);

struct Heap {
    vector<Variable*> heap{nullptr};

    static int parent_ind(int ind) { return ind/2; }
    static int l_child_ind(int ind) { return ind*2; }
    static int r_child_ind(int ind) { return ind*2+1; }
    int max_child_ind(int i) const {
        if (i*2+1 < heap.size()) { return greater_than(heap[i*2], heap[i*2+1]) ? i*2 : i*2+1; } 
        else if (i*2 < heap.size()) { return i*2; }
        else { return i; }
    }

    void insert(Variable*);
    void remove(Variable*);
    void move_up(Variable*);
    void move_down(Variable*);
};

void backtrack();

#endif