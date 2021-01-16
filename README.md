# SAT Solving Project 2: DPLL Solver

**Required Python package:** seaborn

---

- **dpll_solver.cpp**

    `dpll_solver.cpp` implements a DPLL SAT solver. The basic setting of this solver does not apply pure literal elimination or any branching heuristics. These can be activated by adding flags on the terminal. We have implemented eight heuristics. Static Literal Individual Sum (SLIS) and Static Literal Combined Sum (SLCS) use the same principles as DLIS and DLCS but including satisfied clauses. Therefore, they do not need to keep track of active occurrences of variables. We got inspired by the techniques used in CDCL solvers and implemented Backtrack_count as our own heuristic: A variable's priority is the number of times it has been set and backtracked.

    To compile `dpll_solver.cpp`:
    ```
    clang++ -std=c++17 -O3 -DNDEBUG -o dpll_solver dpll_solver.cpp
    ```
    Then you will find the `dpll_solver` executable file in your directory.

    To run `dpll_solver`:
    ```
    ./dpll_solver <path to a cnf file> [-p] [heuristics]
    ```
    -p enables pure literal elimination
    The heutistics options are: -slis, -slcs, -dlis, -dlcs, -bc, -mom, -boehm, -jw


- **record_data.py**

    `record_data.py` stores the solving time for every configuration in a file. We have 18 configurations in total (each heuristic is tested with and without pure literal elimination) and we hardcoded them in the script. The file will not be created if the given filename already exists. All the cnf files that should be used are passed as arguments to the script. The script can be run as follows:
    ```
    python record_data.py <path to dpll_solver> <timeout in seconds> <file to write results to> <cnf files>
    ```
    We have included `sat_stats` and `unsat_stats` in the folder. It contains the solving time for our 18 configurations on the given sat and unsat benchmarks with a timeout of 200 seconds. 


- **display_plot.py**

    `display_plot.py` merges multiple stats files and displays them as a cactus plot. The plot shows how many instances a configuration of our solver can solve within a certain amount of time. The script can be run as follows:
    ```
    python display_plot <stats files generated by record_data.py>
    ```

    We have included `Evaluation.png` in the folder. It shows the performance of our eighteen configurations on the sat and unsat benchmarks.