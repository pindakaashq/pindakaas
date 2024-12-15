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


import java.io.BufferedWriter;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;

import savilerow.Constants;
import savilerow.model.Sat;

public class Power extends BinOp
{
    public static final long serialVersionUID = 1L;
	public Power(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public ASTNode copy() {
	    return new Power(getChild(0), getChild(1));
	}
	
	public boolean toFlatten(boolean propagate) { return true; }
	public boolean isNumerical() {
        return true;
    }
    
	public ASTNode simplify()	{
	    
	    if(getChild(0).isConstant() && getChild(1).isConstant()) {
	        long a=getChild(0).getValue();
	        long b=getChild(1).getValue();
	        if((a==0 && b==0) || b<0) {
	            return null;  // undefined, delay.
	        }
	        return NumberConstant.make(pow(a,b));
	    }
	    if(getChild(1).isConstant() && getChild(1).getValue()==1) {
	        getChild(0).setParent(null);
	        return getChild(0);
	    }
	    
	    return null;
	}
	
	public long getValue() {
	    return pow(getChild(0).getValue(), getChild(1).getValue());
	}

	// Use 0 as a default value, as in SafePower.
	public static long pow(long a, long b) {
	    if((a==0 && b==0) || b<0L) {
	        return 0L;  // Undefined, return default value. 
	    }
	    if(b==0L) {
	        // non-zero a.
	        return 1L;
	    }
	    
	    if(b>Integer.MAX_VALUE) {
	        // Can't use b as an argument to BigInteger.pow
	        if(a==0L || a==1L) {
	            return a;
	        }
	        else if(a==-1) {
	            return (b%2 == 0)?1:-1;
	        }
	        else if(a<-1) {
	            if(b%2 == 0) {
	                return Long.MAX_VALUE;   // Negative to an even power.
	            }
	            else {
	                return Long.MIN_VALUE;   // negative to an odd power.
	            }
	        }
	        else {   // a>1
	            return Long.MAX_VALUE;  // +infty
	        }
	    }
	    return Intpair.BigIntegerToLong(BigInteger.valueOf(a).pow((int) b));
	}
	
	// Lots of cases.
	//  a^b  
	//  Upper bound:
	//  max(a)^max(b) 
	//  (if a is negative, or the negative part is larger than the positive) min(a)^max(b)  or min(a)^(max(b)-1) if max(b) is odd 
	
	// Lower bound:
	// min(a)^min(b)
	
	// (if min(a) is negative) min(a)^max(b) or min(a)^(max(b)-1) (for case where max(b) is even)
	// 
	
	public Intpair getBounds() {
	    Intpair a=getChild(0).getBounds();
        Intpair b=getChild(1).getBounds();
        
        long exp1=b.upper;
        long exp2=b.upper-1;
        long explow=b.lower;
        // put the new bounds into b.
        
        b.upper=Math.max(pow(a.upper, exp1), 
            Math.max(pow(a.lower, exp1),
                pow(a.lower, exp2)));
        
        b.lower=Math.min(pow(a.lower, explow),
            Math.min(pow(a.lower, exp1),
                pow(a.lower, exp2)));
        
        if(getChild(1).isConstant()) {
            long exponent=getChild(1).getValue();
            if(exponent>0 && exponent%2==0 && b.lower<0) {
                b.lower=0;
            }
        }
        
        return b;
	}
	public ArrayList<Intpair> getIntervalSetExp() {
	    ArrayList<Intpair> a=getChild(0).getIntervalSetExp();
	    ArrayList<Intpair> b=getChild(1).getIntervalSetExp();
	    
	    if(Intpair.numValues(a)*Intpair.numValues(b)>Constants.intervallim) {
	        // Just use the bounds.
	        return super.getIntervalSetExp();
	    }
	    
	    ArrayList<Intpair> c=new ArrayList<Intpair>();
	    for(int i=0; i<a.size(); i++) {
	        for(long val1=a.get(i).lower; val1<=a.get(i).upper; val1++) {
	            for(int j=0; j<b.size(); j++) {
	                for(long val2=b.get(j).lower; val2<=b.get(j).upper; val2++) {
	                    long power=pow(val1, val2);
	                    c.add(new Intpair(power, power));
	                }
	            }
	        }
	    }
	    Intpair.normalise(c);
	    return c;
    }
	
	public void toMinionWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException
	{
	    b.append("pow(");
	    getChild(0).toMinion(b, false);
	    b.append(", ");
	    getChild(1).toMinion(b, false);
	    b.append(", ");
	    aux.toMinion(b, false);
	    b.append(")");
	}
	
	public String toString() {
	    return "("+getChild(0)+"**"+getChild(1)+")";
	}
	
	public void toMinizinc(StringBuilder b,  boolean bool_context) {
	    assert(!bool_context);
	    b.append("pow(");
	    getChild(0).toMinizinc(b, bool_context);
	    b.append(",");
	    getChild(1).toMinizinc(b, bool_context);
	    b.append(")");
	}
	
	////////////////////////////////////////////////////////////////////////////
	//
	//   SAT encoding
	
    public void toSATWithAuxVar(Sat satModel, ASTNode auxVar) throws IOException {
        satModel.ternaryEncoding(this, auxVar);
    }
    
    public boolean test(long val1, long val2, long aux) {
        return pow(val1,val2)==aux;
    }
    public long func(long val1, long val2) {
        return pow(val1,val2);
    }
}