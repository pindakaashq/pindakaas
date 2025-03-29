#!/usr/bin/env python3
import pindakaas as pk

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

    for clause in cnf:
        for lit in clause:
            print(f"{lit}, ", end="")
        print("\n", end="")

    wcnf = pk.Wcnf()
    a = wcnf.add_variable()
    b,c = wcnf.add_variables(2)
    wcnf.add_clause([~a,b]) # ~a \/ b
    wcnf.add_clause([(~b).var(),c]) # b \/ c
    # TODO add weighted clause

    cadical = pk.Cadical() # "inherits" from ClauseDatabase
    a = cadical.add_variable()
    b = cadical.add_variable()
    cadical.add_clause([a,b])
    cadical.add_clause([~a,~b])
    print("x", cadical.solve())
    assert cadical.solve() is True # Return True (SAT), False (UNSAT), None (UNKNOWN)
    assert cadical.value(a) is not cadical.value(b)
    assert cadical.solve(assumptions=[a]) is True # Solve with assumptions
    assert cadical.value(a) is True
    assert cadical.value(b) is False
    assert cadical.solve(assumptions=[b]) is True
    assert cadical.value(a) is False
    assert cadical.value(b) is True
    assert cadical.solve(assumptions=[~a, ~b]) is False 
    print(f"{cadical.fail(a)=}")
    print(f"{cadical.fail(b)=}")

    kissat = pk.Kissat()
    a = kissat.add_variable()
    kissat.add_clause([a])
    assert kissat.solve() is True
    try:
        kissat.solve(assumptions=[a]) # but Kissat does not support assumptions
    except TypeError as e:
        print(f"Caught '{e}' of type {type(e)}") # TODO maybe make this friendlier
    assert kissat.value(a) is True
    exit(0)

    # TODO translate pysat's pigeonhole problem to pindakaas

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
