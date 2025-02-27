#!/usr/bin/env python3
import pindakaas as pk


def main():

    cnf = pk.Cnf()
    a,b,c = cnf.add_variables(3)
    cnf.add_clause([~a,b]) # ~a \/ b
    cnf.add_clause([abs(~b),c]) # ~b \/ c
    # print(f"{cnf}")
    cnf = pk.Cnf(5) # this Cnf already has 5 vars
    e = cnf.add_variable()
    print(f"Starting from 5: {cnf}")
    cnf.add_clause([~a,b,e]) # ~a \/ b
    print(f"Adding a clause: {cnf}")

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

# PROPOSED

# Future:
    # cnf.add_linear(cnf, (2*a) + (3*b) + (5*c) <= 6) # Low priority: more overloading to create constraint objects

# Add IPASIR-Python crate
    solver = pk.CadicalSolver() # or pk.Solver(name="cadical")
    # solver.set_terminate_callback(lambda x: False)
    a = solver.add_variable()
    b = solver.add_variable()
    solver.add_clause([a,b])
    solver.add_clause([~a,~b])
    assert solver.solve() is True
    print(f"{solver.value(a)}")
    assert solver.value(a) != solver.value(b)

    # import numpy as np
    # n = 4
    # m = 3
    # php = Cnf()
    # pigeons = { (i,j): solver.add_variable()
    #            for i in range(n)
    #            for j in range(m)
    #            }
    # for i in range(n):
    #     php.add_linear([])

# res = solver.solve(ter = lambda x: print("")) # solve interface similar to IPASIR

if __name__ in "__main__":
    main()
