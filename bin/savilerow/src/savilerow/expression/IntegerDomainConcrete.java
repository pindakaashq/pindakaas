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

// Like an integer domain but contains only constants in a single interval.
// Also only works for int, not long.
// Cannot be open at either end.

public class IntegerDomainConcrete extends SimpleDomain
{
    public static final long serialVersionUID = 1L;
    
    private int lower;
    private int upper;
    
    public IntegerDomainConcrete(int l, int u)
    {
        super();
        lower=l;
        upper=u;
    }
    
    public ASTNode copy() {
	    return new IntegerDomainConcrete(lower, upper);
	}
	
	@Override
    public boolean equals(Object b) {
        if (! (b instanceof IntegerDomainConcrete)) {
            return false;
        }
        
        IntegerDomainConcrete c=(IntegerDomainConcrete) b;
        
        return c.lower==lower && c.upper==upper;
    }
    
    @Override
    public int hashCode() {
        if(hashCache==Integer.MIN_VALUE) {
            int hash = 2251 + (5227*lower) + (1723*upper);
            hashCache=hash;  // store
            return hash;
        }
        else {
            return hashCache;
        }
    }
	
    public Intpair getBounds() {
        return new Intpair(lower,upper);
    }
    public PairASTNode getBoundsAST() {
        return new PairASTNode(NumberConstant.make(lower), NumberConstant.make(upper));
    }
    
    public ArrayList<Intpair> getIntervalSet()
    {
        ArrayList<Intpair> intervals=new ArrayList<Intpair>(1);
        intervals.add(getBounds());
        return intervals;
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
        if(lower==upper) {
            return "int("+lower+")";
        }
        else {
            return "int("+lower+".."+upper+")";
        }
    }
    
    public boolean containsValue(long val) {
        return val>=lower && val<=upper;
    }
}
