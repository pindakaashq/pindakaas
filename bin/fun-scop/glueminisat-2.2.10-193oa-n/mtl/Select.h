/******************************************************************************************[Sort.h]
Copyright (c) 2003-2007, Niklas Een, Niklas Sorensson
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

#ifndef Minisat_Select_h
#define Minisat_Select_h

#include "mtl/Vec.h"
#include "mtl/Sort.h"    // added by nabesima

//=================================================================================================
// Some selection algorithms for vec's


namespace GlueMiniSat {

// modified by nabesima
//#ifndef Minisat_Sort_h
//template<class T>
//struct LessThan_default {
//    bool operator () (T x, T y) { return x < y; }
//};
//#endif

template <class T, class LessThan>
T select(T* array, int size, int nth, LessThan lt)
{
    T           pivot = array[size / 2];
    T           tmp;
    int         i = -1;
    int         j = size;

    for(;;){
        do i++; while(lt(array[i], pivot));
        do j--; while(lt(pivot, array[j]));

        if (i >= j) break;

        tmp = array[i]; array[i] = array[j]; array[j] = tmp;
    }

    if (nth == i) return array[i];
    if (i > nth) return select(array, i, nth, lt);
    else         return select(&array[i], size - i, nth - i, lt);
}
template <class T> static inline T select(T* array, int size, int nth) {
    return select(array, size, nth, LessThan_default<T>()); }


//=================================================================================================
// For 'vec's:


template <class T, class LessThan> T select(vec<T>& v, int nth, LessThan lt) {
    return select((T*)v, v.size(), nth, lt); }
template <class T> T select(vec<T>& v, int nth) {
    return select(v, nth, LessThan_default<T>()); }


//=================================================================================================
}

#endif
