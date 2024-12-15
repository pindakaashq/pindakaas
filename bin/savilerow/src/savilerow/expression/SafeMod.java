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

// Mod with 0 default value when the r.h.s. is 0. 

public class SafeMod extends BinOp
{
    public static final long serialVersionUID = 1L;
	public SafeMod(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public ASTNode copy()
	{
	    return new SafeMod(getChild(0), getChild(1));
	}
	
	public ASTNode simplify()	{
	    
	    if(getChild(0).isConstant() && getChild(1).isConstant()) {
	        long a=getChild(0).getValue();
	        long b=getChild(1).getValue();
	        if(b==0) {
	            return NumberConstant.make(0);   /// Default value.
	        }
	        
	        return NumberConstant.make(mod(a,b));
	    }
	    return null;
	}
	
	public long mod(long a, long b) {
	    return Intpair.BigIntegerToLong(BigInteger.valueOf(a).subtract(BigInteger.valueOf(Divide.div(a, b)).multiply(BigInteger.valueOf(b))));
	    //return a- (long)(Math.floor(((double)a)/((double)b))*b);
	}
	
	public Intpair getBounds() {
	    Intpair num=getChild(0).getBounds();
	    Intpair denom=getChild(1).getBounds();
	    
        // Base could be positive or negative.
        denom.upper=denom.upper-1;
        denom.lower=denom.lower+1;
        
        // Make sure the default value 0 is in range.
        if(denom.upper<0) denom.upper=0;
        if(denom.lower>0) denom.lower=0;
        
        return denom;
	}
	
	public ArrayList<Intpair> getIntervalSetExp() {
        ArrayList<Intpair> a=getChild(0).getIntervalSetExp();
        ArrayList<Intpair> b=getChild(1).getIntervalSetExp();
        
        if(Intpair.numValues(a)*Intpair.numValues(b)>Constants.intervallim) {
            return super.getIntervalSetExp();
        }
        
        ArrayList<Intpair> c=new ArrayList<Intpair>();
        for(int i=0; i<a.size(); i++) {
            for(long val1=a.get(i).lower; val1<=a.get(i).upper; val1++) {
                for(int j=0; j<b.size(); j++) {
                    for(long val2=b.get(j).lower; val2<=b.get(j).upper; val2++) {
                        if(val2!=0L) {
                            long mod=mod(val1,val2);
                            c.add(new Intpair(mod, mod));
                        }
                    }
                }
            }
        }
        c.add(new Intpair(0,0));  // Add default value.
        Intpair.normalise(c);
        return c;
    }
	
	public boolean toFlatten(boolean propagate) { return true;}
	public boolean isNumerical() {
        return true;
    }
    
	public void toMinionWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException {
	    b.append("modulo_undefzero(");
	    getChild(0).toMinion(b, false);
	    b.append(",");
	    getChild(1).toMinion(b, false);
	    b.append(",");
	    aux.toMinion(b, false);
	    b.append(")");
	}
	
	//  WARNING -- the following output methods drop the default value.
	public String toString() {
	    return "("+getChild(0)+"%"+getChild(1)+")";
	}
	public void toMinizinc(StringBuilder b, boolean bool_context) {
	    b.append("(");
	    getChild(0).toMinizinc(b, false);
	    b.append(" mod ");
	    getChild(1).toMinizinc(b, false);
	    b.append(")");
	}
	
	////////////////////////////////////////////////////////////////////////////
	//
	//   SAT encoding
	
    public void toSATWithAuxVar(Sat satModel, ASTNode auxVar) throws IOException {
        satModel.ternaryEncoding(this, auxVar);
    }
    
    public boolean test(long val1, long val2, long aux) {
        if(val2==0) return aux==0;
        return mod(val1, val2)==aux;
    }
    public long func(long val1, long val2) {
        if(val2==0) return 0;
        return mod(val1, val2);
    }
}