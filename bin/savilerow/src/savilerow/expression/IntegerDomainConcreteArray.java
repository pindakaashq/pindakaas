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


import java.util.ArrayList;
import java.util.Arrays;

// Like an integer domain but contains only constants in a set of intervals.
// Not allowed to be infinite or empty.

public class IntegerDomainConcreteArray extends SimpleDomain
{
    public static final long serialVersionUID = 1L;
    
    private long[] intervals;  //  To be interpreted as pairs.  Not to be modified.
    
    public IntegerDomainConcreteArray(long[] in) {
        super();
        assert in.length>=2;
        assert in.length%2==0;
        intervals=in;
    }
    public IntegerDomainConcreteArray(ArrayList<Intpair> in) {
        super();
        assert in.size()>=1;
        intervals=new long[in.size()*2];
        for(int i=0; i<in.size(); i++) {
            intervals[i*2]=in.get(i).lower;
            intervals[i*2+1]=in.get(i).upper;
        }
    }
    
    public ASTNode copy() {
        //  Does not copy the array.
	    return new IntegerDomainConcreteArray(intervals);
	}
	
	@Override
	public ASTNode simplify() {
	    // Must be one canonical form of an integer set. Must reduce this to pair repn if possible. 
	    if(intervals.length==2 && intervals[0]>=Integer.MIN_VALUE && intervals[1]<=Integer.MAX_VALUE) {
	        return new IntegerDomainConcrete((int) intervals[0], (int) intervals[1]);
	    }
	    return null;
	}
	
	@Override
    public boolean equals(Object b) {
        if (! (b instanceof IntegerDomainConcreteArray)) {
            return false;
        }
        
        IntegerDomainConcreteArray c=(IntegerDomainConcreteArray) b;
        return Arrays.equals(intervals, c.intervals);
    }
    
    @Override
    public int hashCode() {
        if(hashCache==Integer.MIN_VALUE) {
            int hash = 5651 + Arrays.hashCode(intervals);
            hashCache=hash;  // store
            return hash;
        }
        else {
            return hashCache;
        }
    }
    
    public Intpair getBounds() {
        return new Intpair(intervals[0],intervals[intervals.length-1]);
    }
    public PairASTNode getBoundsAST() {
        return new PairASTNode(NumberConstant.make(intervals[0]), NumberConstant.make(intervals[intervals.length-1]));
    }
    
    public ArrayList<Intpair> getIntervalSet()
    {
        ArrayList<Intpair> ret=new ArrayList<Intpair>(intervals.length/2);
        for(int i=0; i<intervals.length; i=i+2) {
	        ret.add(new Intpair(intervals[i], intervals[i+1]));
	    }
        return ret;
    }
    
    @Override
    public boolean isFiniteSetUpper() {
        return true;
    }
    @Override
    public boolean isFiniteSetLower() {
        return true;
    }
    @Override
    public boolean isFiniteSet() {
        return true;
    }
    @Override
    public boolean isConstantSet() {
        return true;
    }
    
    public boolean toFlatten(boolean propagate) {return false;}
    
    public String toString() {
        StringBuilder b=new StringBuilder();
        b.append("int(");
        for(int i=0; i<intervals.length; i=i+2) {
            if(intervals[i]==intervals[i+1]) {
                b.append(intervals[i]);
            }
            else {
                b.append(intervals[i]); b.append(".."); b.append(intervals[i+1]);
            }
	        if(i<intervals.length-2) b.append(",");
	    }
	    b.append(")");
        return b.toString();
    }
    
    public boolean containsValue(long val) {
        for(int i=0; i<intervals.length; i=i+2) {
            if(val>=intervals[i] && val<=intervals[i+1]) {
                return true;
            }
        }
        return false;
    }
}
