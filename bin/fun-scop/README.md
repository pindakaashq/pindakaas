# Fun-sCOP

## Entry Info

- Entry
  - This Fun-sCOP solver will enter the main CSP track (sequential) with 2 solver configurations.
	- 1st one uses a SAT solver "kissat"
  - 2nd one uses a SAT solver "GlueMiniSat 2.2.10 193 Order Encoding Adapted Version"

- Notations in the following
| DIR       | It stands for the directory where you place scop                     |
| TMPDIR    | It is the directory where the solver is allowed to                   |
|           | create temporary files                                               |
| BENCHNAME | It stands for the name of the instance file (with its extension)     |

- Solver URL
  - https://tsoh.org/sCOP/

- License
  - see LICENSE.txt

## Requirements for Fun-sCOP

- Java 8
- SAT Solvers and their requirements

## How to install SAT solvers

You can use install-sat-solvers.sh.
Or please read the following instructions. 

- (for Sequential CSP 1) Kissat
   - (URL) https://github.com/arminbiere/kissat
   - Final products we need is the executable `build/kissat`
   - Its installation command is as follows:
   - Please install it by `./configure && make`
```
cd DIR/kissat
./configure && make
```

- (for Sequential CSP 2) GlueMiniSat 2.2.10 193 Order Encoding Adapted Version
   - Final products we need is the executable `simp/glueminisat-simp-2.2.10-193oa-n-release`
   - Its installation command is as follows:
```
cd DIR/glueminisat-2.2.10-193oa-n/simp/
make clean
make r
```

- lzma (os command)
   - we assume an OS command 'lzma' is available for decomposing
     *.xml.lzma instances.
     - lzma is called from Fun-sCOP. 
   - If there is no 'lzma' then simply give *.xml to Fun-sCOP.

## How to run

  - (NOTE) Fun-sCOP performs better the larger the memory.
- We here assume 32GB can be allocated to JVM. But larger heap size is better if possible.
  - assume that the following command is executed in the 'scop-for-xcsp23' directory.
  - (Sequential CSP 1) using Kissat
    ```
    DIR/scop.sh 11g DIR/scop.jar -hybrid DIR/kissat/build/kissat default TMPDIR BENCHNAME
    ```
  - (Sequential CSP 2) using GlueMiniSat with -order option
    ```
    DIR/scop.sh 11g DIR/scop.jar -order DIR/glueminisat-2.2.10-193oa-n/simp/glueminisat-simp-2.2.10-193oa-n-release -model:-verb=3:-elim-cl=5000000:-native-oa TMPDIR BENCHNAME
    ```

- Example (please refer http://xcsp.org/series for example XCSP3 instances)
  - We here assume 32GB can be allocated to JVM. But larger heap size is better if possible.
  - assume that the following command is executed in the 'scop-for-xcsp23' directory.
```
./scop.sh 11g scop.jar -hybrid kissat/build/kissat default /tmp examples/AllInterval-007.xml
```

## Overview of Fun-sCOP

  - Fun-sCOP is a Sat-based COnstraint Programming system written in
    Scala 2.12.
  - Fun-sCOP aims to be a re-implementation of Sugar (Tamura et al.) 
    written in Java. Many things are imported from Sugar (software
    design, normalization, and encoding).
  - Currently, main differences are as follows:
    - XCSP3 instances is accepted as input in Fun-sCOP.
    - Encoding of extensional constraints is different between the two
      systems.
    - Some of encoding heuristics is different between the two systems.
    - Log encoding (from CSP into SAT) is implemented by using the BDD
      encoding (Een and Sorensson).
  - It can use 3 encoding methods:
    - the order encoding
    - the log encoding
    - the hybrid encoding integrating the two encodings above. 
  - It works as follows:
    1. encode a XCSP3 file into a DIMACS CNF file.
    2. launch a SAT solver to solve the encoded CNF file.
    3. the output of the SAT solver is decoded to the solution of the
       XCSP3 instance. 

## Components of Fun-sCOP

- scop.jar
    - It is a fat jar containing all resources except non-Java SAT solvers.
      - XCSP3-Java-Tools
        (https://github.com/xcsp3team/XCSP3-Java-Tools) by XCSP3 Team.
      - Fun-sCOP
      - scala standard libraries (version 2.12)
- Sat4j by Daniel Le Berre et al. 
	- Sat4j is a java library for solving boolean satisfaction and optimization problems.
	- It can solve SAT, MAXSAT, Pseudo-Boolean, Minimally Unsatisfiable Subset (MUS) problems.
	- Being in Java, the promise is not to be the fastest one to solve those problems (a SAT solver in Java is about 3.25 times slower than its counterpart in C++), but to be full featured, robust, user friendly, and to follow Java design guidelines and code conventions.

