/******************************************************************************************[Heap.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

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

#ifndef GlueMiniSat_MUPQueue_h
#define GlueMiniSat_MUPQueue_h

#include "mtl/Vec.h"
#include "mtl/Map.h"

namespace GlueMiniSat {

//=================================================================================================
// A heap implementation with support for decrease/increase key.


class MUPQueue {
    vec<int>  heap;     // Heap of integers
    int       cap;      // Max capacity of heap

    // Index "traversal" functions
    static inline int left  (int i) { return i*2+1; }
    static inline int right (int i) { return (i+1)*2; }
    static inline int parent(int i) { return (i-1) >> 1; }


    void percolateUp(int i) {
        int x  = heap[i];
        int p  = parent(i);

        while (i != 0 && x < heap[p]){
            heap[i] = heap[p];
            i       = p;
            p       = parent(p);
        }
        heap[i] = x;
    }

    void percolateDown(int i) {
        int x = heap[i];
        while (left(i) < heap.size()){
            int child = right(i) < heap.size() && (heap[right(i)] < heap[left(i)]) ? right(i) : left(i);
            if (!(heap[child] < x)) break;
            heap[i] = heap[child];
            i       = child;
        }
        heap[i] = x;
    }


  public:
    MUPQueue(int capacity) : cap(capacity) { }

    int  size      ()          const { return heap.size(); }
    bool empty     ()          const { return heap.size() == 0; }
    int  operator[](int index) const { assert(index < heap.size()); return heap[index]; }

    void enqueue(int n) {
        if (heap.size() < cap) {
            heap.push(n);
            percolateUp(heap.size() - 1);
        }
        else if (n > heap[0]) {
            heap[0] = n;
            if (heap.size() > 1) percolateDown(0);
        }
    }

    int dequeue() {
        int x            = heap[0];
        heap[0]          = heap.last();
        heap.pop();
        if (heap.size() > 1) percolateDown(0);
        return x;
    }

    void clear(bool dealloc = false) {
        heap.clear(dealloc);
    }

    double avg() {
        double total = 0;
        for (int i=0; i < heap.size(); i++)
            total += heap[i];
        return total / heap.size();
    }

    void print() const {
        for (int i=0; i < heap.size(); i++)
            printf("%d ", heap[i]);
        printf("\n");
    }
};


//=================================================================================================
}

#endif
