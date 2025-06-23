#!/usr/bin/env python
import pindakaas

# Instantiate solver, create two new literals, and encode a XOR constraint
slv = pindakaas.solver.CaDiCaL()
x, y, z = slv.new_vars(3)
slv += x ^ y

with slv.solve(assumptions=[x]) as result:
    assert result.value(x) is True
    assert result.value(y) is False

with slv.solve(assumptions=[x, y]) as result:
    assert result.status == pindakaas.solver.Status.UNSATISFIABLE
