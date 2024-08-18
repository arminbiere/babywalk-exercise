BabyWalk Local Search SAT Solver
--------------------------------

This is a simple locals search SAT solver.

It has been been used as a template for a project in our SAT solving course
and is used in our live-hacking part of our tutorial at the summer school.

Your task is to search for `TODO` and fill in that code.

If you run `configure && make test` the solver is built and regression
tests in `test` are run.  Only trivial unsatisfiable and otherwise
simple satisfiable instances are used.  Still your solver is expected to
solve those small satisfiable ones.  If solved the model checker
'checkmodel' checks the output to satisfy the formula.

There is also the `generate` too which can produce some random formulas,
that you can also use for testing.  The clauses are all of the same length
and default is to produce 3-SAT formulas at the hardness threshold (with
4.267 more clauses than variables).  With `-p` as option the tool plants
a solution and thus makes sure the formula is satisfiable.
