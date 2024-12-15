#!/usr/bin/python
import os
# load the data files and turn them into Minion car sequencing instances
# using the carsequencing script

def mkinstances(f, i):
    os.system("./carseq2param.py --file=carseqdata/%s >carSequencing%d.param"%(f, i))
    
for i in range(5):
    f="reginpuget%d.car"%i
    mkinstances(f, i+1)
    
for i in range(5, 80):
    f="csplib-instance-%d"%i
    mkinstances(f, i+1)
    
