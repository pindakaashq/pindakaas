#!/usr/bin/env python3
import pindakaas as pk


def main():
    cnf = pk.Cnf()
    a,b,c = cnf.add_variables(3)
    cnf.add_clause([~a,b]) # ~a \/ b
    cnf.add_clause([abs(~b),c]) # ~b \/ c
    cnf = pk.Cnf(5) # More or less temporary work-around, starting with 5 vars
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
    cnf.add_linear([a,b,c]) # a + b + c >= 1 == a \/ b \/ c

    for clause in cnf:
        for lit in clause:
            print(f"{lit}, ", end="")
        print("\n", end="")

    solver = pk.CadicalSolver() # should "inherit" from Cnf/ClauseDatabase
    a = solver.add_variable()
    b = solver.add_variable()
    solver.add_clause([a,b])
    solver.add_clause([~a,~b])
    assert solver.solve() is True # Return True (SAT), False (UNSAT), None (UNKNOWN)
    print(f"{solver.value(a)}") # Also True/False/None
    assert solver.value(a) != solver.value(b)
    assert solver.solve() is True # Return True (SAT), False (UNSAT), None (UNKNOWN)
    print(f"2nd {solver.value(a)}") # Also True/False/None

    exit(0)

    # TODO: for completing CPMpy standard: timeouts
    # assert solver.solve(time_limit=datetime.duration(10))

    # TODO: all solutions
    for sol in solver.solutions():
        print(f"{sol}")

    # TODO beyond: solver selection, encoder selection, improve implied constraints
    # `pip install pindakaas[solver]`
    solver = pk.Solver(name="kissat")

    # TODO nice to have:
    cnf.add_linear(cnf, (2*a) + (3*b) + (5*c) <= 6) # Low priority: more overloading to create constraint objects

if __name__ in "__main__":
    main()
