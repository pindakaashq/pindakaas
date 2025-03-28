#!/usr/bin/env python3
import pindakaas as pk

def main():
    cnf = pk.Cnf()
    a = cnf.add_variable()
    b,c = cnf.add_variables(2)
    cnf.add_clause_from_slice([~a,b]) # ~a \/ b
    cnf.add_clause([(~b).var(),c]) # b \/ c
    # Not allowed: cnf.add_clause([-1,-2]) # `TypeError: argument 'clause': 'int' object cannot be converted to 'Lit'`

    ccnf = cnf.with_conditions([a,b])
    ccnf.add_clause_from_slice([c]) # (-1 /\ -2) -> 3
    print(f"CCNF {ccnf}")
    print(f"CNF {cnf}")

    try:
        cnf.add_clause([])
    except pk.Unsatisfiable as e:
        print(f"Caught Unsatisfiable exception: {e} of type {type(e)}")

    # ccnf = cnf.with_conditions([~c])
    # cnf.add_clause([a,b])

    cnf = pk.Cnf(5) # More or less temporary work-around, starting with 5 vars
    e = cnf.add_variable()
    print(f"Starting from 5: {cnf}")
    cnf.add_clause([~a,b,e]) # ~a \/ b
    print(f"Adding a clause: {cnf}")

    # 2*a + 3*b + 5*c <= 6
    cnf.add_linear([a,b,c], coefficients=[2,3,5], comparator=pk.Comparator.LessEq, k=6)
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
    # TODO add and test Wcnf features



    cadical = pk.Cadical() # should "inherit" from Cnf/ClauseDatabase
    a = cadical.add_variable()
    b = cadical.add_variable()
    cadical.add_clause([a,b])
    cadical.add_clause([~a,~b])
    assert cadical.solve([a,b]) is True # Return True (SAT), False (UNSAT), None (UNKNOWN)
    assert cadical.value(a) is not cadical.value(b)

    kissat = pk.Kissat()
    a = kissat.add_variable()
    kissat.add_clause([a])
    assert kissat.solve([a,b]) is True
    assert kissat.value(a) is True

    # solver = pk.Solver()

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
