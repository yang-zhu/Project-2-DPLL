#ifndef DPLL_SOLVER_H
#define DPLL_SOLVER_H

#include <iostream>
#include <fstream> 
#include <vector>
#include <set> 
#include <deque> 
#include <string>
#include <cassert>
#include <map>
#include <cmath> 
#include <limits>
#include <cstdlib>

using namespace std;

struct Variable;

struct Clause {
    Variable* sat_var = nullptr;  // the variable that first satisfies the clause
    vector<int> lits;
    int active;

    Clause(vector<int> lits, int active) : lits{lits}, active{active} {}
};

// A variable is either unset, false or true.
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
    int active_pos_occ = 0;  // Keep track of the occurrence of a positive literal in active clauses.
    int active_neg_occ = 0;  // Keep track of the occurrence of a negative literal in active clauses.
    int heap_position = 0;  // A variable's position in the heap, which is used to update the heap.
    map<int,int> pos_by_cl_len;  // the occurrences of a positive literal in active clauses, sorted by clause length
    map<int,int> neg_by_cl_len;  // the occurrences of a negative literal in active clauses, sorted by clause length
    double jw_pos = 0;  // Jeroslow-Wang heuristic score for positive literal
    double jw_neg = 0;  // Jeroslow-Wang heuristic score for negative literal
    int backtrack_count = 0;  // for the backtrack_count heuristic
    void set(Value, Mark);
    void unset();
};

enum class Heuristic {
    none, slis, slcs, dlis, dlcs, backtrack_count, mom, boehm, jw
};

bool greater_than(Variable*, Variable*);

struct Heap {  // a max-heap
    vector<Variable*> heap{nullptr}; // Add a dummy element to simplify index computation.

    static int parent_ind(int ind) { return ind/2; }  // Return the index of the parent node of a node.
    static int l_child_ind(int ind) { return ind*2; }  // Return the index of the left child of a node.
    static int r_child_ind(int ind) { return ind*2+1; }  // Return the index of the right child of a node.
    // Return the index of the child with the maximum priority. When there is no child, return the index of the node.
    int max_child_ind(int i) const { 
        if (i*2+1 < heap.size()) { return greater_than(heap[i*2], heap[i*2+1]) ? i*2 : i*2+1; } 
        else if (i*2 < heap.size()) { return i*2; }
        else { return i; }
    }

    void insert(Variable*);
    void remove(Variable*);
    void move_up(Variable*);
    void move_down(Variable*);
    Variable* max();
};

void pure_lit();

void backtrack();

#endif