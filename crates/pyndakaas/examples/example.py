#!/usr/bin/env python
import pindakaas

# Instantiate solver, create two new literals, and encode a XOR constraint
slv = pindakaas.solver.CaDiCaL()
x, y, z = slv.new_vars(3)
slv += x ^ y

# Solve and inspect status and literal values
with slv.solve() as result:
    assert result.status == pindakaas.solver.Status.SATISFIED
    assert result.value(x) != result.value(y)
