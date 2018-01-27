# MSA_SAT_Solver
Multithread simulated annealing mini SAT solver

1. Usage
    1. to compile: make
    1. to test some cnf file: ./yasat <filename.cnf>
1. Features
    1. VSIDS score strategy with integer type, score decaying
    1. BCP with two literal watching
    1. Conflict Driven Clause Learning with Non-chronological backtracking
    1. Random Restart
    1. Random Parallel Clause Learning
    1.Random Branch
    1.Random Resolution Stage Random Backtracking Simulated Annealing
1. Summary
    1. Parameters for Randomness Really Matters
    1. Size of Clause database really hurts the Speed, we may need to add some clause evaluation method to determine whether to add the learnt clause or not.
