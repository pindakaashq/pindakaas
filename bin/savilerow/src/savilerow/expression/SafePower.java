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
import java.util.ArrayList;

import savilerow.Constants;
import savilerow.model.Sat;

public class SafePower extends BinOp
{
    public static final long serialVersionUID = 1L;
	public SafePower(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public ASTNode copy() {
	    return new SafePower(getChild(0), getChild(1));
	}
	
	public boolean toFlatten(boolean propagate) { return true; }
	public boolean isNumerical() {
        return true;
    }
    
	public ASTNode simplify() {
	    if(getChild(0).isConstant() && getChild(1).isConstant()) {
	        long a=getChild(0).getValue();
	        long b=getChild(1).getValue();
	        if((a==0 && b==0) || b<0) {
	            return NumberConstant.make(0);
	        }
	        return NumberConstant.make(Power.pow(a,b));
	    }
	    if(getChild(1).isConstant() && getChild(1).getValue()==1) {
	        getChild(0).setParent(null);
	        return getChild(0);
	    }
	    
	    return null;
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
	    
	    b.upper=Math.max( Power.pow(a.upper, exp1), 
	        Math.max(Power.pow(a.lower, exp1),
	            Power.pow(a.lower, exp2)));
	    
	    b.lower=Math.min( Power.pow(a.lower, explow),
	        Math.min(Power.pow(a.lower, exp1),
	            Power.pow(a.lower, exp2)));
	    
	    // Add zero for undef
	    if(b.upper < 0) b.upper=0;
	    if(b.lower > 0) b.lower=0;
	    
	    // If target is Minion, will use normal power ct which defines 0^0 as 1. 
	    // So add 1 as default value. 
	    if(b.upper < 1) b.upper=1;
	    if(b.lower > 1) b.lower=1;
	    
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
	                    long power=Power.pow(val1, val2);
	                    c.add(new Intpair(power, power));
	                }
	            }
	        }
	    }
	    //  No need to add default value. Power.pow returns 0 when power is undefined. 
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
	
	// WARNING -- rest of these drop 'safe' default value.
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
        return func(val1, val2)==aux;
    }
    public long func(long val1, long val2) {
        if((val1==0 && val2==0) || val2<0) {
            return 0;
        }
        return Power.pow(val1,val2);
    }
}