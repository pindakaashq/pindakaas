/*******************************************************************************************[Map.h]
Copyright (c) 2006-2010, Niklas Sorensson
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

#ifndef GlueMiniSat_IntSet_h
#define GlueMiniSat_IntSet_h

#include <stdio.h>
#include "mtl/IntTypes.h"
#include "mtl/Vec.h"
#include "mtl/Map.h"
#include "mtl/Sort.h"

namespace GlueMiniSat {

//=================================================================================================
// Hash table implementation of IntSet
//

class IntSet {
 private:
    vec<int>* table;
    int       cap;
    int       sz;

    bool     checkCap(int new_size) const { return new_size > cap; }
    uint32_t index   (const int n)  const { return ((uint32_t)n) % cap; }
    void    _insert  (const int n)        { table[index(n)].push(n); }
    void     rehash () {
        const vec<int>* old = table;

        int old_cap = cap;
        int newsize = primes[0];
        for (int i = 1; newsize <= cap && i < nprimes; i++)
           newsize = primes[i];

        table = new vec<int>[newsize];
        cap   = newsize;

        for (int i = 0; i < old_cap; i++)
            for (int j = 0; j < old[i].size(); j++)
                _insert(old[i][j]);

        delete [] old;
        // printf(" --- rehashing, old-cap=%d, new-cap=%d\n", cap, newsize);
    }


 public:

    IntSet () : table(NULL), cap(0), sz(0) {}
    ~IntSet() { delete [] table; }

    IntSet(const IntSet& other) : table(NULL), cap(0), sz(0) { add(other); }
    IntSet(const IntSet& o1, const IntSet& o2) : table(NULL), cap(0), sz(0) { add(o1); add(o2); }

    IntSet&  operator = (const IntSet& other) {
        clear();
        add(other);
        return *this;
    }

    bool add(const int n) {
        if (checkCap(sz * 2 + 1)) rehash();
        if (has(n)) return false;
        _insert(n);
        sz++;
        return true;
    }

    void add(const IntSet& other) {
        for (int i = 0; i < other.cap; i++)
            for (int j = 0; j < other.table[i].size(); j++)
                add(other.table[i][j]);
    }

    bool has(const int n) const {
        if (sz == 0) return false;
        const vec<int>& ps = table[index(n)];
        for (int i = 0; i < ps.size(); i++)
            if (ps[i] == n)
                return true;
        return false;
    }

    bool containsAll(const IntSet& other) const {
        if (size() < other.size()) return false;
        for (int i = 0; i < other.cap; i++)
            for (int j = 0; j < other.table[i].size(); j++)
                if (!has(other.table[i][j]))
                    return false;
        return true;
    }

    void remove(const int n) {
        if (!has(n)) return;
        vec<int>& ps = table[index(n)];
        int j = 0;
        for (; j < ps.size() && ps[j] != n; j++);
        assert(j < ps.size());
        ps[j] = ps.last();
        ps.pop();
        sz--;
    }

    void clear(bool dealloc=false) {
        if (dealloc) {
            cap = sz = 0;
            delete [] table;
            table = NULL;
        } else {
            sz = 0;
            for (int i = 0; i < cap; i++)
                table[i].clear();
        }
    }

    uint32_t hash() const {
        uint32_t h = 0xAAAAAAAA;
        for (int i = 0; i < cap; i++)
            for (int j = 0; j < table[i].size(); j++)
                h ^= table[i][j];
        return h;
    }

    bool operator == (const IntSet& s) const {
        if (size() != s.size()) return false;
        for (int i = 0; i < cap; i++)
            for (int j = 0; j < table[i].size(); j++)
                if (!s.has(table[i][j]))
                    return false;
        return true;
    }

    int  size() const { return sz; }
    int  bucket_count() const { return cap; }

    // NOTE: the hash and equality objects are not moved by this method:
    void moveTo(IntSet& other){
        delete [] other.table;

        other.table = table;
        other.cap   = cap;
        other.sz  = sz;

        table = NULL;
        sz = cap = 0;
    }

    void print() const {
        vec<int> tmp;
        for (int i = 0; i < cap; i++)
            for (int j = 0; j < table[i].size(); j++)
                tmp.push(table[i][j]);
        sort(tmp);
        for (int i=0; i < tmp.size(); i++)
            printf("%d ", tmp[i]);
    }

    // NOTE: given a bit more time, I could make a more C++-style iterator out of this:
    const vec<int>& bucket(int i) const { return table[i]; }
};

inline uint32_t hash(const IntSet& s) { return s.hash(); }

//=================================================================================================
}

#endif
