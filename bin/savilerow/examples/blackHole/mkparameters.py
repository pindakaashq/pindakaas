#!/usr/bin/env python3

import random

myarr=list(range(1,52))

random.shuffle(myarr)
assert len(myarr)==51
print("letting initialStacks = "+str(myarr))
