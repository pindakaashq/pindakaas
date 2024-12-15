/*************************************************************************************[ExtTable.h]
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

#ifndef CORE_FREQCOUNTER_H_
#define CORE_FREQCOUNTER_H_

#include "mtl/Vec.h"
#include "mtl/Map.h"
#include "mtl/ObjHeap.h"

namespace GlueMiniSat {

//=================================================================================================
template <class D, class H = Hash<D>, class E = Equal<D> >
class FreqCounter {
private:

    struct Item {
        D   data;
        int count;
        int err;
        Item(D& d, int c, int e) : data(d), count(c), err(e) {}
    };

    struct ItemComp     { bool     operator()(const Item* p, const Item* q) const { return p->count < q->count; } };
    struct ItemPtrHash  { uint64_t operator()(const Item* p) const                { return (uint64_t)p; } };
    struct ItemPtrEqual { bool     operator()(const Item* p, const Item* q) const { return p == q; } };

    vec<Item>	      table;       // The set of monitored elements.
    int               max_sz;      // The max size of table.
    double            support;     // The user defined support.
    double            epsilon;     // The user defined error.
    uint64_t 		  num;         // The number of elements.
    Map<D,Item*,H,E>  data2ptr;    // Map data from the pointer.
    ObjHeap<ItemComp,Item*,ItemPtrHash,ItemPtrEqual> heap;

public:
    FreqCounter(int max_size, double sup) : max_sz(max_size), support(sup), epsilon(1.0/max_size), num(0), heap(ItemComp()) {
        table.capacity(max_sz);
    }

    bool inc(D& data) {
        num++;
        if (!data2ptr.has(data)) {
            if (table.size() < max_sz) {
                table.push(Item(data, 1, 0));
                Item* p = &(table.last());
                data2ptr.insert(data, p);
                heap.insert(p);
                return p->count - p->err > support * num;
            }
            // Remove the min element
            Item* p = heap.removeMin();
            data2ptr.remove(p->data);
            p->data = data;
            p->err  = p->count;
            p->count++;
            data2ptr.insert(data, p);
            heap.insert(p);
            return p->count - p->err > support * num;
        }

        Item *p = data2ptr[data];
        p->count++;
        heap.increase(p);
        return p->count - p->err > support * num;
    }

    void     step()       { num++; }
    uint32_t size() const { return num; }

    void print() {
        print(0, 0);
    }

    void print(int idx, int indent) {
        if (heap.size() <= idx) return;
        for (int i=0; i < indent; i++)
            printf(" ");
        Item *p = heap[idx];
        p->data.print();
        printf(" c:%d e:%d\n", p->count, p->err);
        print(idx * 2 + 1, indent + 1);
        print(idx * 2 + 2, indent + 1);
    }

};

}

#endif /* CORE_FREQCOUNTER_H_ */
