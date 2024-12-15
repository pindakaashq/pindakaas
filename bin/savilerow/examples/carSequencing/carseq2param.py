#!/usr/bin/python
# Generate param files for SR from car seq data files.

import math

import sys, os, getopt

(optargs, other)=getopt.gnu_getopt(sys.argv, "", ["file="])

if len(other)!=1:
    print "Usage: carsequencing.py --file=XXXX"
    sys.exit(1)

numcars=10
numoptions=4
numconfs=4

loadfile=False

for i in optargs:
    (a1, a2)=i
    if a1=="--file":
        loadfile=a2

if not loadfile:
    print "No input file provided."
    sys.exit(1)

if loadfile:
    lines=open(loadfile, "r").readlines()
    lines=filter(lambda x:x[0]!="#", lines)
    lines=map(lambda x:x.strip(), lines)
    lines=filter(lambda x:x!="", lines)
    sp=map(lambda x:int(x), lines[0].split())
    numcars=sp[0]
    numoptions=sp[1]
    numconfs=sp[2]
    p=map(lambda x:int(x), lines[1].split())
    q=map(lambda x:int(x), lines[2].split())
    lines=lines[3:]
    confsrequire=[]
    numeachconf=[]
    for line in lines:
        bits=map(lambda x:int(x), line.split())
        confsrequire.append(bits[2:])
        numeachconf.append(bits[1])
        assert bits[0]==len(numeachconf)-1  # in order.

print "language ESSENCE' 1.0"
print "$ loaded file: "+str(loadfile)
print "letting numcars=%d"%(numcars)
print "letting numclasses=%d"%(numconfs)
print "letting numoptions=%d"%(numoptions)
print "letting optMax="+str(p)
print "letting windowSize="+str(q)
print "letting numberPerClass="+str(numeachconf)
print "letting optionsRequired="+str(confsrequire)


