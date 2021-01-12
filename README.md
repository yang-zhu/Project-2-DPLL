# Project-2-DPLL

To compile `dpll_solver.cpp`:
```
clang++ -std=c++17 -O3 -DNDEBUG -o dpll_solver dpll_solver.cpp
```
Then you will find the `dpll_solver` executable file in your directory.
To test `dpll_solver`:
```
./dpll_solver <path to a cnf file> [-p] [heuristics]
```
-p enables pure literal elimination
The heutistics options are: -slis, -slcs, -dlis, -dlcs, -bc, -mom, -boehm, -jw

To test `dpll_solver.py`:
```
python dpll_solver.py <path to a cnf file>
```