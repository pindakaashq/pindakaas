#!/usr/bin/env python3
import pindakaas as pk


def main():

    cnf = pk.Cnf()
    a = cnf.add_variable()
    b = cnf.add_variable()
    c = cnf.add_variable()
    cnf.add_clause([~a,b]) # ~a \/ b
    cnf.add_clause([abs(~b),c]) # ~b \/ c
    print(f"{cnf}")
    cnf = pk.Cnf()

    try:
        cnf.add_clause([])
    except pk.Unsatisfiable as e:
        print(f"Caught Unsatisfiable exception: {e} of type {type(e)}")

    # 2*a + 3*b + 5*c <= 6
    cnf.add_linear([a,b,c], coefficients=[2,3,5], comparator=pk.Comparator.LessEq, k=6)
    # cnf.add_linear(cnf, [a,b,c]) # a + b + c >= 1 == a \/ b \/ c

    for clause in cnf:
        for lit in clause:
            print(f"{lit}, ", end="")
        print("\n", end="")

    return

# PROPOSED

# Future:
    pk.add_linear(cnf, (2*a) + (3*b) + (5*c) <= 6) # Low priority: more overloading to create constraint objects

# This week: solving + 
    pk.solver(name="cadical") # Returns CadicalSolver

# Implement ClauseDatabase as ABC
# Implement Solver as ABC, extends ClauseDatabase


# Add IPASIR-Python crate

    solver = pk.Cadical() # or pk.Solver(name="cadical")
    solver.set_terminate_callback(lambda x: False)
    solver.add_clause([~a,b]) # ~a \/ b (subclass ClauseDatabase)
# res = solver.solve(ter = lambda x: print("")) # solve interface similar to IPASIR

# res can be based off of:
# [derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
# pub enum SolveResult<Sol: Valuation, Fail = ()> {
# 	Satisfied(Sol),
# 	Unsatisfiable(Fail),
# 	Unknown,
# }

# Or:
    solver.value(a) # True
    solver.value(~a) # False


