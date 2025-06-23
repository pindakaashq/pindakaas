#!/usr/bin/env python
import pindakaas

f = pindakaas.CNF()
x, y, z = f.new_vars(3)
f += (x & ~y) | (y == z)  # `x and not y, or y iff z`
f += 2 * x + 3 * y + 5 * z <= 6
print(f.to_dimacs())
