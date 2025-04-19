#!/usr/bin/env python
import sys
import pindakaas as pk
import time
import numpy as np
from datetime import timedelta

try:
    n = int(sys.argv[1])
except IndexError:
    n = 10
m = n - 1

# cadical = pk.Cnf()
cadical = pk.solvers.Cadical()
x = np.fromfunction(
    np.vectorize(lambda i, j: cadical.add_variable()), (n, m), dtype=pk.Lit
)

for row in x:  # each pigeons is in at least one hole
    cadical.add_linear(row.tolist())
for col in x.T:  # each hole has at most one pigeon
    cadical.add_linear(col, comparator=pk.Comparator.LessEq)

timer = time.process_time()

r = cadical.solve(time_limit=timedelta(seconds=1))
print("1.", r, time.process_time() - timer)
assert r is None, f"r={r}"

r = cadical.solve()
print("2.", r, time.process_time() - timer)
assert r is False, f"r={r}"
