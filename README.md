BabyVivify Clause Vivification Preprocessor
-------------------------------------------

This is a simple SAT preprocessor using Vivification.

It is used as a template for the second project in our SAT solving course.
As before search for 'TODO' and fill in that code.  The code as is
compiles but just prints the original formula.  To succeed in this
assignment your preprocessor is supposed to actually vivify
clauses (and generate correct proof traces - see below).

If you run `configure && make test` the solver is built and regression
tests in `test` are run.  If enabled the preprocessor traces resolution
and proof deletion to a proof file, which can then be checked by the
proof checker `checkproof`.  The resulting formula should admit the same
model as the original formula and thus there is also a tool `checkmodel`
which given the preprocessed (or original) CNF checks that the given
solution (in SAT Competition output format with 's SATISFIABLE' and
'v' lines representing the model) satisfies the formula.

The regression suite runs both checkers (the second only if the formula
is satisfiable).  See also [`test/README.md`](test/README.md).
