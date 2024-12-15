package savilerow.expression;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Peter Nightingale
    
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
import java.util.ArrayList;
import java.util.Collections;
import java.util.Objects;

// Obtain the bounds of an expression, for use when generating an aux variable.
// Long.MIN_VALUE and Long.MAX_VALUE are used to indicate an open range

public class Intpair implements Comparable<Intpair> {
    public long lower,upper;
    public Intpair(long l, long u) {lower=l; upper=u;}
    public String toString() {return "("+lower+","+upper+")";}
    
    public boolean isEmpty() {
        return lower>upper;
    }
    
    public Intpair intersect(Intpair other) {
        // Intersect this with the other, and make a new one. 
        long l=(lower<other.lower)?other.lower:lower;
        long u=(upper<other.upper)?upper:other.upper;
        return new Intpair(l, u);
    }
    
    public Intpair intersectNull(Intpair other) {
        // Intersect this with the other, return null if the intersection is empty.
        long l=(lower<other.lower)?other.lower:lower;
        long u=(upper<other.upper)?upper:other.upper;
        if(l>u) return null;
        return new Intpair(l, u);
    }
    
    // Union operation may not be exact. e.g. 1..2 and 10..20 gives 1..20.
    public Intpair union(Intpair other) {
        long l=(lower<other.lower)?lower:other.lower;
	    long u=(upper>other.upper)?upper:other.upper;
	    return new Intpair(l, u);
    }
    
    //  Merge adjacent or overlapping intervals into one interval. 
    public Intpair merge(Intpair other) {
        if(upper < other.lower-1 || lower-1 > other.upper) {  //  3..5,6..10 should merge. 
            // can't be merged into one pair. 
            return null;
        }
        
        long l=(lower<other.lower)?lower:other.lower;
        long u=(upper<other.upper)?other.upper:upper;
        return new Intpair(l, u);
    }
    
    public ArrayList<Intpair> subtract(Intpair other) {
        // Do this / other and return a new Intpair if there is a change. 
        Intpair intersection=this.intersect(other);
        
        ArrayList<Intpair> ret=new ArrayList<Intpair>();
        
        // the piece lower than intersection
        long l1=lower;
        long u1=upper<(intersection.lower-1)?upper:(intersection.lower-1);
        
        // The piece above intersection
        long l2=lower>(intersection.upper+1)?lower:(intersection.upper+1);
        long u2=upper;
        
        Intpair new1=new Intpair(l1, u1);
        if(! new1.isEmpty()) ret.add(new1);
        
        Intpair new2=new Intpair(l2, u2);
        if(! new2.isEmpty()) ret.add(new2);
        
        return ret;
    }
    
    // Sort first by lowerbound then upperbound
    public int compareTo(Intpair other) {
        if(lower>other.lower) {
            return 1;
        }
        else if(lower==other.lower) {
            if(upper>other.upper) {
                return 1;
            }
            else if(upper==other.upper) {
                return 0;
            }
            else {
                return -1;
            }
        }
        else {
            // lower<o.lower
            return -1;
        }
    }
    
    @Override
    public boolean equals(Object other) {
        if(! (other instanceof Intpair)) {
            return false;
        }
        Intpair i=(Intpair) other;
        return i.lower == lower && i.upper == upper;
    }
    @Override
    public int hashCode() {
        return 3853 + Objects.hash(lower, upper);
    }
    
    public Intpair copy() {
        return new Intpair(lower, upper);
    }
    
    public static boolean in(ArrayList<Intpair> list, long val) {
        for(int i=0; i<list.size(); i++) {
            if(val>=list.get(i).lower && val<=list.get(i).upper) {
                return true;
            }
        }
        return false;
    }
    
    // Convert BigInteger to long with saturation i.e. values larger than long max are mapped to long max. 
    static public long BigIntegerToLong(BigInteger b) {
        if(b.compareTo(BigInteger.valueOf(Long.MIN_VALUE)) <= 0) {
            return Long.MIN_VALUE;
        }
        else if(b.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) >= 0) {
            return Long.MAX_VALUE;
        }
        else {
            return b.longValue();
        }
    }
    
    // Convert an arraylist of Intpair to a domain. 
    // isBool indicates to make  a BooleanDomain
    public static ASTNode makeDomain(ArrayList<Intpair> a, boolean isBool) {
        normalise(a);  //  Make sure a is in the normal form.
        
        if(isBool) {
            assert a.size()<=1;
            assert a.size()==0 || ( a.get(0).lower>=0 && a.get(0).upper<=1 );
            
            if(a.size()==0) {
                return new BooleanDomain(new EmptyRange());
            }
            if(a.get(0).lower==0 && a.get(0).upper==1) {
                return new BooleanDomainFull();
            }
            
            return new BooleanDomain(new Range(NumberConstant.make(a.get(0).lower), NumberConstant.make(a.get(0).upper)));
        }
        
        // Need a special case for infinite domain open both ends.
        /*if(a.size()==1 && a.get(0).lower==Long.MIN_VALUE && a.get(0).upper==Long.MAX_VALUE) {
            return new IntegerDomain(new Range(null, null));
        }*/
        
        //  Special case for single interval that fits in ints.
        if(a.size()==1 && a.get(0).lower>=Integer.MIN_VALUE && a.get(0).upper<=Integer.MAX_VALUE) {
            return new IntegerDomainConcrete((int) a.get(0).lower, (int) a.get(0).upper);
        }
        if(a.size()>=1 && a.get(0).lower>Long.MIN_VALUE && a.get(a.size()-1).upper<Long.MAX_VALUE) {
            //  If non-empty and finite, use the concrete array type.
            return new IntegerDomainConcreteArray(a);
        }
        if(a.size()==0) {
            return new IntegerDomain(new EmptyRange());
        }
        
        ArrayList<ASTNode> out2=new ArrayList<ASTNode>();
        
        for(int i=0; i<a.size(); i++) {
            Intpair pr=a.get(i);
            if(pr.lower==pr.upper) {
                out2.add(NumberConstant.make(pr.lower));
            }
            else {
                ASTNode cl1;
                if(pr.lower==Long.MIN_VALUE) {
                    cl1=null;
                }
                else {
                    cl1=NumberConstant.make(pr.lower);
                }
                
                ASTNode cl2;
                if(pr.upper==Long.MAX_VALUE) {
                    cl2=null;
                }
                else {
                    cl2=NumberConstant.make(pr.upper);
                }
                
                out2.add(new Range(cl1, cl2));
            }
        }
        
        return new IntegerDomain(out2);
    }
    
    // Convert a single interval to a domain. 
    // isBool indicates to make  a BooleanDomain
    public static ASTNode makeDomain(long lower, long upper, boolean isBool) {
        if(isBool) {
            if(lower==0 && upper==1) {
                return new BooleanDomainFull();
            }
            
            return new BooleanDomain(new Range(NumberConstant.make(lower), NumberConstant.make(upper)));
        }
        
        if(lower<Integer.MIN_VALUE || upper>Integer.MAX_VALUE) {
            return new IntegerDomain(new Range(NumberConstant.make(lower), NumberConstant.make(upper)));
        }
        else {
            return new IntegerDomainConcrete((int) lower, (int) upper);
        }
    }
    
    public static long numValues(ArrayList<Intpair> list) {
        assert list!=null;
        long a=0;
        for(int i=0; i<list.size(); i++) {
            a=a+list.get(i).upper-list.get(i).lower+1;
        }
        return a;
    }
    
    //  Transform an interval set by multiplying by a constant.
    public static ArrayList<Intpair> multIntervalSet(ArrayList<Intpair> l, long mult) {
        if(mult==1) {
            return l;
        }
        else if(mult==-1) {
            ArrayList<Intpair> out=new ArrayList<Intpair>(l.size());
            for(int i=l.size()-1; i>=0; i--) {  /// reverse order of pairs.
                Intpair p=new Intpair(-l.get(i).upper, -l.get(i).lower);   //  reverse order of each pair
                out.add(p);
            }
            return out;
        }
        else {
            ArrayList<Intpair> out=new ArrayList<Intpair>();
            if(mult>0) {
                for(int i=0; i<l.size(); i++) {
                    for(long j=l.get(i).lower; j<=l.get(i).upper; j++) {
                        out.add(new Intpair(j*mult, j*mult));
                    }
                }
            }
            else {
                // reverse order
                for(int i=l.size()-1; i>=0; i--) {
                    for(long j=l.get(i).upper; j>=l.get(i).lower; j--) {
                        out.add(new Intpair(j*mult, j*mult));
                    }
                }
            }
            return out;
        }
    }
    
    //  Scales up an interval set without punching holes in the intervals. 
    public static ArrayList<Intpair> scaleIntervalSet(ArrayList<Intpair> l, long mult) {
        ArrayList<Intpair> out=new ArrayList<Intpair>(l.size());
        if(mult>0) {
            for(int i=0; i<l.size(); i++) {
                out.add(new Intpair(l.get(i).lower*mult, l.get(i).upper*mult));
            }
        }
        else {
            // reverse order of list and intervals.
            for(int i=l.size()-1; i>=0; i--) {
                out.add(new Intpair(l.get(i).upper*mult, l.get(i).lower*mult));
            }
        }
        return out;
    }
    
    public static ArrayList<Intpair> shiftIntervalSet(ArrayList<Intpair> l, long shift) {
        for(Intpair p : l) {
            p.lower+=shift;
            p.upper+=shift;
        }
        return l;
    }
    
    //  Return union of a and b. Does not recycle any objects from a or b, or the lists a or b themselves.
    public static ArrayList<Intpair> union(ArrayList<Intpair> a, ArrayList<Intpair> b) {
        // a and b must be in order
        ArrayList<Intpair> out=new ArrayList<Intpair>(a.size()+b.size());
        
        int loca=0;
        int locb=0;
        //System.out.println("Unioning: "+a+"  and  "+b);
        
        // Step along a and b, merging as necessary and adding intervals to out.
        while(loca<a.size() || locb<b.size()) {
            if(loca==a.size()) {
                // Reached the end of a. Just add an interval from b.
                out.add(b.get(locb).copy());
                locb++;
            }
            else if(locb==b.size()) {
                // Same for a.
                out.add(a.get(loca).copy());
                loca++;
            }
            else {
                // Check if the two intervals are non-overlapping
                Intpair ia=a.get(loca);
                Intpair ib=b.get(locb);
                if(ia.upper+1 < ib.lower) {
                    out.add(ia.copy());
                    loca++;
                }
                else if(ib.upper+1 < ia.lower) {
                    out.add(ib.copy());
                    locb++;
                }
                else {
                    // The two intervals touch or overlap.
                    Intpair m=ia.merge(ib);
                    assert m!=null;
                    loca++;
                    locb++;
                    //  Keep on merging from lists a and b until no longer possible. 
                    while(loca<a.size() || locb<b.size()) {
                        boolean cont=false;
                        if(loca<a.size()) {
                            Intpair m2=m.merge(a.get(loca));
                            if(m2 != null) {
                                m=m2;
                                loca++;
                                cont=true;
                            }
                        }
                        if(locb<b.size()) {
                            Intpair m2=m.merge(b.get(locb));
                            if(m2 != null) {
                                m=m2;
                                locb++;
                                cont=true;
                            }
                        }
                        if(!cont) break;
                    }
                    
                    out.add(m);
                }
            }
        }
        
        //System.out.println(" into "+out);
        
        //assert numValues(out)==numValues(a)+numValues(b)-numValues(intersection(a, b));
        //assert numValues(out)==numValues(a)+numValues(setDifference(b, a));
        return out;
    }
    
    // Given an arraylist of intpair, put it into the normal form -- i.e. in 
    // ascending order, with touching intervals merged. 
    public static void normalise(ArrayList<Intpair> a) {
        Collections.sort(a);
        
        //  merge touching or overlapping intervals.  Adds nulls to the list.
        for(int i=0; i<a.size(); i++) {
            if(a.get(i)!=null) {
                int j=i+1;
                while(j<a.size()) {
                    Intpair m=a.get(i).merge(a.get(j));
                    if(m!=null) {
                        a.set(i, m);
                        a.set(j, null);
                        j++;
                    }
                    else {
                        break;  // exit the while loop. No more merging to be done.
                    }
                }
            }
        }
        
        //  Remove nulls. 
        int ipos=0;
        for(int i=0; i<a.size(); i++) {
            if(a.get(i)!=null) {
                a.set(ipos, a.get(i));
                ipos++;
            }
        }
        
        a.subList(ipos, a.size()).clear();
    }
    
    //   Intersect two sets of intervals.  Assumes both are in normal form. 
    public static ArrayList<Intpair> intersection(ArrayList<Intpair> a, ArrayList<Intpair> b) {
        ArrayList<Intpair> out=new ArrayList<Intpair>();
        
        int mark=0;  // either 0, or the last interval seen in b that had a non-empty intersection with
        // an interval in a. 
        for(int aloc=0; aloc<a.size(); aloc++) {
            for(int bloc=mark; bloc<b.size(); bloc++) {
                Intpair blah=a.get(aloc).intersectNull(b.get(bloc));
                if(blah != null) {
                    out.add(blah);
                    mark=bloc;
                }
                else if(b.get(bloc).lower>a.get(aloc).upper) {
                    break;  //  No more b's can intersect current a. 
                }
            }
        }
        return out;
    }
    
    //  Subtract set b from a. 
    public static ArrayList<Intpair> setDifference(ArrayList<Intpair> a, ArrayList<Intpair> b) {
        return intersection(a, complement(b));
    }
    
    public static ArrayList<Intpair> complement(ArrayList<Intpair> a) {
        ArrayList<Intpair> out=new ArrayList<Intpair>(a.size()+1);
        
        if(a.size()==0) {
            out.add(new Intpair(Long.MIN_VALUE, Long.MAX_VALUE));
        }
        else {
            if(a.get(0).lower!=Long.MIN_VALUE) {
                out.add(new Intpair(Long.MIN_VALUE, a.get(0).lower-1));
            }
            
            // Between each pair.
            for(int i=0; i<a.size()-1; i++) {
                out.add(new Intpair(a.get(i).upper+1, a.get(i+1).lower-1));
            }
            
            //  Top
            if(a.get(a.size()-1).upper!=Long.MAX_VALUE) {
                out.add(new Intpair(a.get(a.size()-1).upper+1, Long.MAX_VALUE));
            }
        }
        return out;
    }
    
    //  Does it contain a value. Binary search, assumes a is in order.
    public static boolean contains(ArrayList<Intpair> a, long val) {
        int upper=a.size()-1;
        int lower=0;
        while(lower<=upper) {
            int mid=lower + (upper-lower)/2;
            if(val < a.get(mid).lower) {
                upper=mid-1;
            }
            else if(val > a.get(mid).upper) {
                lower=mid+1;
            }
            else {
                //  val must be in a.get(mid)
                return true;
            }
        }
        return false;
    }
    
    //  Find the location (index) of val within the list of Intpair. 0-based indexing. 
    //  Returns -1 for not found. 
    public static long location(ArrayList<Intpair> a, long val) {
        long valsLeft=0;  //  Values to the left of the current interval.
        for(int i=0; i<a.size(); i++) {
            Intpair current=a.get(i);
            if(val>=current.lower && val<=current.upper) {
                return valsLeft+val-current.lower;
            }
            else {
                valsLeft=valsLeft+current.upper-current.lower+1;
            }
        }
        return -1;
    }
    
    //  Find the interval for a value.
    //  Returns -1 for not found. 
    public static int intervalForVal(ArrayList<Intpair> a, long val) {
        int upper=a.size()-1;
        int lower=0;
        while(lower<=upper) {
            int mid=lower + (upper-lower)/2;
            if(val < a.get(mid).lower) {
                upper=mid-1;
            }
            else if(val > a.get(mid).upper) {
                lower=mid+1;
            }
            else {
                //  val must be in a.get(mid)
                return mid;
            }
        }
        return -1;
    }
    
    //  Index into set of intervals as if it is just an arraylist of long.
    public static long lookup(ArrayList<Intpair> a, long idx) {
        for(int i=0; i<a.size(); i++) {
            Intpair current=a.get(i);
            long cursize=current.upper-current.lower+1;
            if(idx < cursize) {
                return current.lower+idx;
            }
            else {
                idx=idx-cursize;
            }
        }
        assert false;
        return 0;
    }
    
    public static String printValues(ArrayList<Intpair> a) {
        StringBuilder b=new StringBuilder();
        for(int i=0; i<a.size(); i++) {
	        for(long val=a.get(i).lower; val<=a.get(i).upper; val++) {
                b.append(String.valueOf(val));
                if(i<a.size()-1 || val<a.get(i).upper) b.append(",");
	        }
	    }
	    return b.toString();
    }
    
    public static ArrayList<Intpair> makeList(long lower, long upper) {
        assert upper >= lower;
        ArrayList<Intpair> a=new ArrayList<Intpair>();
        a.add(new Intpair(lower, upper));
        return a;
    }
}
