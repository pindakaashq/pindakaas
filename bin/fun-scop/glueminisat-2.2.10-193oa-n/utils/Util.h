/*
 * Util.h
 *
 *  Created on: 2014/03/09
 *      Author: nabesima
 */

#ifndef UTIL_H_
#define UTIL_H_

inline int numbits(uint32_t bits)
{
    bits = (bits & 0x55555555) + (bits >> 1 & 0x55555555);
    bits = (bits & 0x33333333) + (bits >> 2 & 0x33333333);
    bits = (bits & 0x0f0f0f0f) + (bits >> 4 & 0x0f0f0f0f);
    bits = (bits & 0x00ff00ff) + (bits >> 8 & 0x00ff00ff);
    return (bits & 0x0000ffff) + (bits >>16 & 0x0000ffff);
}

#endif /* UTIL_H_ */
