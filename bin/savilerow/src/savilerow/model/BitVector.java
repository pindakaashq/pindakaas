package savilerow.model;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Ewan Davidson, Peter Nightingale
    
    This file is part of Savile Row.
    
    Savile Row is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    
    Savile Row is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    
    You should have received a copy of the GNU General Public License
    along with Savile Row.  If not, see <http://www.gnu.org/licenses/>.

*/

import java.math.BigInteger;

import savilerow.CmdFlags;
import savilerow.expression.Intpair;

public class BitVector {

    public static int bits = 64;
    public static long highest = 0;
    public static long lowest = 0;

    public static void addMax(Intpair max) {

        if (lowest > max.lower) { lowest = max.lower; }
        if (highest < max.upper) { highest = max.upper; }
    }

    public static void determineBits() {

        int lowerBits = bitsNeeded(lowest*-1);
        int higherBits = bitsNeeded(highest+1);

        bits = lowerBits;
        if (higherBits > lowerBits) { bits = higherBits; }
        bits++;
        if (bits > 64) {
            CmdFlags.errorExit("Values are too large\n This model contains integers that require" +
                    "more than 64 bits to represent");
        }
    }

    public static int bitsNeeded(long value) {

        int bits = 0;

        do {
            value = value/2;
            bits++;
        }
        while (value != 0);

        return bits;
    }

    public static long toLong(String x) {

        char [] xArray = x.toCharArray();

        if (xArray[1] == 'x') {
            // System.out.println("hex");

            xArray[0] = '0';
            x = String.valueOf(xArray);
            long a = Long.decode(x);
            return a;
        }
        else {

            xArray = x.substring(2,x.length()).toCharArray();
            long returnValue;

            if (xArray[0] == '1') {

                xArray = subtractOne(xArray);
                xArray = flipBits(xArray);
                returnValue = -1*(new BigInteger(String.valueOf(xArray), 2)).longValue();
            }
            else { returnValue = new BigInteger(String.valueOf(xArray), 2).longValue(); }

            return returnValue;
        }
    }

    /*
     * Returns the value as hexadecimal string.
     * Will return a binary string if hex isn't possible.
     */
    public static String toHexString(long x) {

        char[] inBin;

        if (x < 0) {

            inBin = toBinary(x*-1);
            inBin = flipBits(inBin);
            inBin = addOne(inBin);
        }
        else { inBin = toBinary(x); }

        if (bits%4 == 0) {

            char[] inHex = toHex(inBin);
            return "#x" + String.valueOf(inHex);
        }

        return "#b" + String.valueOf(inBin);
    }

    public static char[] toHex(char[] inBin) {

        char[] inHex = new char[bits/4];

        for (int i = 0, j =0; i < inHex.length; i++, j+=4) {

            inHex[i] = hexDigit(inBin[j], inBin[j+1],inBin[j+2],inBin[j+3]);
        }

        return inHex;
    }

    public static char[] toBinary(long x) {

        char[] inBin = new char[bits];

        inBin[0] = '0';
        long rem = x;

        for (int i = 1, p = bits-2; i < inBin.length-1; i++, p--) {

            long bit = rem/powerOfTwo(p);

            if (bit == 0) { inBin[i] = '0'; }
            else { inBin[i] = '1';  }

            rem = rem%powerOfTwo(p);
        }

        if (rem == 0) { inBin[bits-1] = '0'; }
        else { inBin[bits-1] = '1'; }

        return inBin;
    }

    private static long powerOfTwo(int n) {
        assert n>=1 && n<=62;
        return 1L<<n;
    }

    /*
    This is why java should support some kind of pattern matching!!!!
     */
    public static char hexDigit(char a, char b, char c, char d) {

        if (a == '1') {

            if (b == '1') {

                if (c == '1') {

                    if (d == '1') { return 'f'; }
                    else { return 'e'; }
                }
                else {

                    if (d == '1') { return 'd'; }
                    else { return 'c'; }
                }
            }
            else {

                if (c == '1') {

                    if (d == '1') { return 'b'; }
                    else { return 'a'; }
                }
                else {

                    if (d == '1') { return '9'; }
                    else { return '8'; }
                }
            }
        }
        else {

            if (b == '1') {

                if (c == '1') {

                    if (d == '1') { return '7'; }
                    else { return '6'; }
                }
                else {

                    if (d == '1') { return '5'; }
                    else { return '4'; }
                }
            }
            else {

                if (c == '1') {

                    if (d == '1') { return '3'; }
                    else { return '2'; }
                }
                else {

                    if (d == '1') { return '1'; }
                    else { return '0'; }
                }
            }
        }
    }


    public static char[] flipBits(char[] x) {

        for (int i = 0; i < x.length; i++) {

            if (x[i] == '0') { x[i] = '1'; }
            else { x[i] = '0'; }
        }

        return x;
    }

    public static char[] addOne(char[] x) {

        for (int i = x.length-1; i >= 0; i--) {

            if (x[i] == '1') { x[i] = '0'; }
            else {

                x[i] = '1';
                break;
            }
        }

        return x;
    }

    public static char[] subtractOne(char[] x) {

        for (int i = x.length-1; i >= 0; i--) {

            if(x[i] == '1') {

                x[i] = '0';
                i++;

                while (i < x.length) {
                    x[i] = '1';
                    i++;
                }
                break;
            }
        }

        return x;
    }

    public static int getBits() { return bits; }
}
