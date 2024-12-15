/***********************************************************************************[PremiseLits.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
  2008 - Gilles Audemard, Laurent Simon

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef PremiseLits_h
#define PremiseLits_h

#include "mtl/Vec.h"

namespace GlueMiniSat {

//=================================================================================================

class PremisesSet {
    Lit      *premise;
    int      *nums;
    int       columns;
    int       rows;
    uint32_t  counter;

    int index(const Lit p) const { return toInt(p) * columns; };

public:
     PremisesSet() : premise(NULL), nums(NULL), columns(0), rows(0), counter(0) {}
    ~PremisesSet() { delete[] premise; delete[] nums; }

    void init(int num_vars, int num_premises) {
        delete[] premise;
        delete[] nums;
        rows    = num_vars * 2;
        columns = num_premises;
        premise = new Lit[rows * columns];
        nums    = new int[rows];
        for (int i=0; i < num_vars; i++) {
            Lit pos = mkLit(i, false);
            Lit neg = mkLit(i, true );
            for (int j=0; j < num_premises; j++) {
                premise[index(pos) + j] = pos;
                premise[index(neg) + j] = neg;
            }
            nums[toInt(pos)] = nums[toInt(neg)] = 0;
        }
    }

    // p implies q
    bool add(Lit p, Lit q) {
        // Avoid registering the duplicated premise literal.
        Lit *ps = &premise[index(q)];

//        printf("add index = %d\n", index(q));
//        printf("before\n");
//        for (int i=0; i < columns; i++)
//            printf("%d, ", toInt(ps[i]));
//        printf("\n");

        Lit pre = ps[0];
        ps[0] = p;
        for (int i=1; i < columns; i++) {
            if (pre == p) return false;  // already registered.
            Lit tmp = ps[i];
            ps[i] = pre;
            pre   = tmp;
        }
        nums[toInt(q)] = (nums[toInt(q)] + 1) % columns;

//        printf("after\n");
//        for (int i=0; i < columns; i++)
//            printf("%d, ", toInt(ps[i]));
//        printf("\n");

        return true;
    }

    inline       Lit  last  (Lit q) const { return  premise[index(q)]; }
    inline const Lit* head(Lit q) const { return &premise[index(q)]; }
    inline       Lit  get   (Lit q)       {
        int num = nums[toInt(q)];
        return num == 0 ? q : premise[index(q) + (counter++) % num];
    }
};

//=================================================================================================
}
#endif
