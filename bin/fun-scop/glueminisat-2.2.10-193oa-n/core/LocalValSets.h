/***********************************************************************************[LocalVals.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson
Copyright (c) 2011-2016, Hidetomo Nabeshima

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

#ifndef GlueMiniSat_LocalValSets_h
#define GlueMiniSat_LocalValSets_h

#include "mtl/Vec.h"

namespace GlueMiniSat {

//=================================================================================================

struct ValSet {
    uint32_t  sum;
    uint32_t  num;
    ValSet() : sum(0), num(0) {}
    void clear() { sum = num = 0; }
    void add  (uint32_t val) { sum += val; num++; }
};

class LocalValSets {
    vec<ValSet> buf;
    int       	first;
    int		  	end;
    uint64_t  	total;
    uint32_t    num;
    int       	cap;
    int       	sz;
    int			wait_time;

public:
    LocalValSets() : first(0), end(0), total(0), num(0), cap(0), sz(0), wait_time(0) {
    }

    void init(int size, int wtime=0) {
        buf.growTo(size);
        clear();
        cap = size;
        wait_time = wtime;
    }

    void push(ValSet vals) {
        if (cap==0) return;
        if (sz==cap) {
            assert(end==first); // The queue is full, next value to enter will replace oldest one
            total -= buf[end].sum;
            num   -= buf[end].num;
            if ((++end) == cap) end = 0;
        } else
            sz++;
        total += vals.sum;
        num   += vals.num;
        buf[first] = vals;
        if ((++first) == cap) first = 0;
        if (wait_time > 0) wait_time--;
    }

    uint64_t sum()     const { return total; }
    double   average() const { return (double)total / (double)num; }
    bool     ready()   const { return wait_time == 0 && sz == cap; }
    int      size()    const { return sz; }
    void     wait(int w)     { wait_time = w; }

    void 	 clear() 		 { first = 0; end = 0; sz = 0; total = 0; num = 0; }
};

//=================================================================================================
}

#endif
