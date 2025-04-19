#!/usr/bin/env python
import pindakaas as pk
from datetime import timedelta

def main():
    cnf = pk.Cnf()
    a = cnf.add_variable()
    b,c = cnf.add_variables(2)
    cnf.add_clause([~a,b]) # ~a \/ b
    cnf.add_clause([(~b).var(),c]) # b \/ c
    # Not allowed: cnf.add_clause([-1,-2]) # `TypeError: argument 'clause': 'int' object cannot be converted to 'Lit'`

    # TODO unfortunately, doesn't quite work.
    # with cnf.with_conditions([a,b]) as ccnf:
    #     ccnf.add_clause([c]) # (-1 /\ -2) -> 3
    #     cnf.add_linear([a,b,c], coefficients=[2,3,5], comparator=pk.Comparator.LessEq, k=6)
    #     print(f"CCNF {ccnf}") # TODO not sure why still available but ok
    #     print(f"CNF {cnf}")
    # exit(0)
    
    try:
        cnf.add_clause([])
    except pk.Unsatisfiable as e:
        print(f"Caught Unsatisfiable exception: {e} of type {type(e)}")

    # 2*a + 3*b + 5*c <= 6
    cnf.add_linear([a,b,c], coefficients=[2,3,5], comparator=pk.Comparator.LessEq, k=6)
    p = cnf.add_variable()
    cnf.add_linear([a,b,c], coefficients=[2,3,5], comparator=pk.Comparator.LessEq, k=6, conditions=[~p])
    cnf.add_linear([a,b,c]) # a + b + c >= 1 == a \/ b \/ c

    # for clause in cnf:
    #     for lit in clause:
    #         print(f"{lit}, ", end="")
    #     print("\n", end="")

    wcnf = pk.Wcnf()
    a = wcnf.add_variable()
    b,c = wcnf.add_variables(2)
    wcnf.add_clause([~a,b]) # ~a \/ b
    wcnf.add_clause([(~b).var(),c]) # b \/ c
    # TODO add weighted clause

    for solver in [pk.solvers.Cadical(), pk.solvers.IntelSat()]: # assumption supporting solvers
        a = solver.add_variable() # any solver "inherits" from
        b = solver.add_variable()
        solver.add_clause([a,b])
        solver.add_clause([~a,~b])
        solver.solve(time_limit=5)
        assert solver.solve() is True # Return True (SAT), False (UNSAT), None (UNKNOWN)
        assert solver.value(a) is not solver.value(b)
        assert solver.solve(assumptions=[a]) is True # Solve with assumptions
        assert solver.value(a) is True
        assert solver.value(b) is False
        assert solver.solve(assumptions=[b]) is True
        assert solver.value(a) is False
        assert solver.value(b) is True
        assert solver.solve(assumptions=[~a, ~b]) is False 
        print(f"{solver.fail(a)=}")
        print(f"{solver.fail(b)=}")

    kissat = pk.solvers.Kissat()
    a = kissat.add_variable()
    kissat.add_clause([a])
    assert kissat.solve() is True
    try:
        kissat.solve(assumptions=[a]) # but Kissat does not support assumptions
    except TypeError as e:
        print(f"Caught '{e}' of type {type(e)}") # TODO maybe make this friendlier
    assert kissat.value(a) is True

    cadical = pk.solvers.Cadical() # "inherits" from ClauseDatabase
    a,b,c = cadical.add_variables(3)
    p = list(cadical.add_variables(4))
    cadical.add_clause([a])
    cadical.add_clause([~c])
    cadical.add_clause([~p[0],~a,b])
    cadical.add_clause([~p[1],~b,c])
    cadical.add_clause([~p[2],~c,a])
    cadical.add_clause([~p[3],~a,c])

    ls = [a,b,c] + p
    if cadical.solve(assumptions=p) is True:
        for l in ls:
            print(f"value of {l} {cadical.value(l)}")
    else:
        for l in ls:
            print(f"failed of {l} {cadical.fail(l)}")
        core = list(p for p in p if not cadical.fail(p))
        assert cadical.solve(assumptions=core) is False
        core = list(p for p in p if not cadical.fail(p))
        for l in ls:
            print(f"failed of {l} {cadical.fail(l)}")

    # print(f"{solver.value(a)}") # Also True/False/None
    # assert solver.value(a) != solver.value(b)
    # TODO: for completing CPMpy standard: timeouts
    # assert solver.solve(time_limit=datetime.duration(10))

    # TODO: all solutions
    # for sol in solver.solutions():
    #     print(f"{sol}")

    # TODO beyond: solver selection, encoder selection, improve implied constraints
    # `pip install pindakaas[solver]`
    # solver = pk.Solver(name="kissat")

    # print(f"2nd {solver.value(a)}") # Also True/False/None
    # TODO nice to have:
    # cnf.add_linear(cnf, (2*a) + (3*b) + (5*c) <= 6) # Low priority: more overloading to create constraint objects

if __name__ in "__main__":
    main()
