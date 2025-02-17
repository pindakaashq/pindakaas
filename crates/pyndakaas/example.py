#!/usr/bin/env python3
import pindakaas as pk

cnf = pk.Cnf()
a = cnf.new_var()
b = cnf.new_var()
c = cnf.new_var()
cnf.add_clause([~a,b]) # ~a \/ b
cnf.add_clause([abs(~b),c]) # ~b \/ c
print(f"{cnf}")
cnf = pk.Cnf()

try:
    cnf.add_clause([])
except pk.Unsatisfiable as e:
    print(f"Caught Unsatisfiable exception: {e} of type {type(e)}")

# 2*a + 3*b + 5*c <= 6
pk.encode(cnf, [a,b,c], coefficients=[2,3,5], comparator=pk.Comparator.LessEq, k=6)
pk.encode(cnf, [a,b,c]) # a + b + c >= 1 == a \/ b \/ c
# pk.encode(cnf, (2*a) + (3*b) + (5*c) <= 6) # Idea

for clause in cnf:
    for lit in clause:
        print(f"{lit}, ", end="")
    print("\n", end="")
