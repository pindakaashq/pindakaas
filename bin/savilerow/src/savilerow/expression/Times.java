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

import savilerow.*;
import savilerow.model.*;

public class Times extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
	public Times(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public Times(ArrayList<ASTNode> args) {
	    super(args);
	}
	
	public Times(ASTNode[] ch) {
	    super(ch);
	}
	
	public ASTNode copy()
	{
	    return new Times(getChildrenArray());
	}
	
	// Turn it into a constant or sum if possible.
	// Turning it into a WeightedSum allows it to be gathered into the parent, if the
	// parent is a WeightedSum.
	public ASTNode simplify()
	{
	    ArrayList<ASTNode> c=getChildren();
	    boolean changed=false;
	    
	    long constants=1;
	    for(int i=0; i<c.size(); i++) {
	        if(c.get(i).isConstant()) {
	            if(constants!=1) {
	                changed=true;  // Only set the flag if this is the second non-1 constant found. 
	            }
	            constants=multiply(constants, c.get(i).getValue());
	            c.remove(i);
	            i--;
	        }
	        else if( (!CmdFlags.getOutputReady()) && c.get(i) instanceof Times) {
	            // We are not in "output ready" mode,
	            // Collect it into here. 
	            changed=true;
	            c.addAll(c.get(i).getChildren());
	            c.remove(i);
	            i--;
	        }
	    }
	    
	    if(constants==0) {
	        // Special case, if the product contains a 0 throw it all away
	        return NumberConstant.make(0);
	    }
	    
	    if(c.size()==0) {
	        return NumberConstant.make(constants);
	    }
	    
	    if(c.size()==1) {
	        // If there is only one non-constant left. 
	        c.get(0).setParent(null);
	        if(constants==1) {
	            return c.get(0);
	        }
	        else {
                ArrayList<Long> l=new ArrayList<Long>();
                l.add(constants);
                return new WeightedSum(c, l);
            }
	    }
	    
	    if(constants!=1) {
	        c.add(NumberConstant.make(constants));
	    }
	    
	    if(changed) {
	        for(int i=0; i<c.size(); i++) {
	            c.get(i).setParent(null);
	        }
	        return new Times(c);
	    }
	    
	    return null;
	}
	
	@Override
	public boolean typecheck(SymbolTable st) {
	    for(int i=0; i<numChildren(); i++) {
	        if(!getChild(i).typecheck(st)) return false;
	        if(getChild(i).getDimension()>0) {
	            CmdFlags.println("ERROR: Unexpected matrix in product: "+this);
	            return false;
	        }
	        if(getChild(i).isSet()) {
	            CmdFlags.println("ERROR: Unexpected set in product: "+this);
	            return false;
	        }
        }
        return true;
    }
	
	@Override
	public ASTNode normalise() {
	    // sort by hashcode 
        ArrayList<ASTNode> ch=getChildren();
        boolean changed=sortByHashcode(ch);
        
        if(changed) return new Times(ch);
        else return this;
	}
	@Override
	public ASTNode normaliseAlpha() {
	    // sort by hashcode 
        ArrayList<ASTNode> ch=getChildren();
        boolean changed=sortByAlpha(ch);
        
        if(changed) return new Times(ch);
        else return null;
	}
	
	public long getValue() {
	    long eval=1;
	    for(int i=0; i<numChildren(); i++) {
	        assert getChild(i).isConstant();
	        eval=multiply(eval, getChild(i).getValue());
	    }
	    return eval;
	}
	
	static long multiply(long a, long b) {
	    //  Saturates at Long.MAX_VALUE and Long.MIN_VALUE
	    return Intpair.BigIntegerToLong(BigInteger.valueOf(a).multiply(BigInteger.valueOf(b)));
	}
	
	public Intpair getBounds()
	{
	    Intpair a=getChild(0).getBounds();
	    for(int i=1; i<numChildren(); i++) {
            Intpair b=getChild(i).getBounds();
            // multiply the four combinations of bounds
            long w=multiply(a.lower, b.lower);
            long x=multiply(a.upper, b.lower);
            long y=multiply(a.lower, b.upper);
            long z=multiply(a.upper, b.upper);
            a.lower=Math.min(w, Math.min(x, Math.min(y,z)));
            a.upper=Math.max(w, Math.max(x, Math.max(y,z)));
	    }
	    return a;
	}
	public ArrayList<Intpair> getIntervalSetExp() {
	    if(numChildren()>2) {
	        return super.getIntervalSetExp(); // Just use the bounds.
	    }
	    ArrayList<Intpair> a=getChild(0).getIntervalSetExp();
	    ArrayList<Intpair> b=getChild(1).getIntervalSetExp();
	    
	    if(Intpair.numValues(a)*Intpair.numValues(b)> Constants.intervallim) {
	        return super.getIntervalSetExp();
	    }
	    
	    ArrayList<Intpair> c=new ArrayList<Intpair>();
	    for(int i=0; i<a.size(); i++) {
	        for(long val1=a.get(i).lower; val1<=a.get(i).upper; val1++) {
	            for(int j=0; j<b.size(); j++) {
	                for(long val2=b.get(j).lower; val2<=b.get(j).upper; val2++) {
	                    long product=val1*val2;
	                    c.add(new Intpair(product, product));
	                }
	            }
	        }
	    }
	    Intpair.normalise(c);
	    return c;
    }
    
	public boolean toFlatten(boolean propagate) { return true;}
	public boolean isNumerical() {
        return true;
    }
    public boolean isCommAssoc() {
        return true;
    }
	
	public String toString() {
	    String st="(";
	    for(int i=0; i<numChildren(); i++) {
	        st+=getChild(i);
	        if(i<numChildren()-1) st+=" * ";
	    }
	    return st+")";
	}
	
	// Binary output methods. 
	
	public void toMinionWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException {
	    assert numChildren()==2;
	    b.append("product(");
	    getChild(0).toMinion(b, false);
	    b.append(", ");
	    getChild(1).toMinion(b, false);
	    b.append(", ");
	    aux.toMinion(b, false);
	    b.append(")");
	}
	
	public void toFlatzincWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException	{
	    assert numChildren()==2;
	    b.append("constraint int_times(");
	    getChild(0).toFlatzinc(b, false);
	    b.append(", ");
	    getChild(1).toFlatzinc(b, false);
	    b.append(", ");
	    aux.toFlatzinc(b, false);
	    b.append(");");
	}
	public void toMinizinc(StringBuilder b, boolean bool_context) {
	    assert numChildren()==2;
	    b.append("(");
	    getChild(0).toMinizinc(b, false);
	    b.append("*");
	    getChild(1).toMinizinc(b, false);
	    b.append(")");
	}
	
	////////////////////////////////////////////////////////////////////////////
	//  
	//  SAT encoding
	
    public void toSATWithAuxVar(Sat satModel, ASTNode auxVar) throws IOException {
        satModel.ternaryEncoding(this, auxVar);
    }
    
    public boolean test(long val1, long val2, long aux) {
        return func(val1, val2)==aux;
    }
    public long func(long val1, long val2) {
        return multiply(val1, val2);
    }
    
	public boolean childrenAreSymmetric() {
	    return true;
	}

	public boolean usesSMTEncoding() { return CmdFlags.getUseBV() || CmdFlags.getUseNIA();  }

	@Override
	public String smtEncodeBV(SMT satModel) {
		if (numChildren() > 2) { CmdFlags.errorExit("too many children"); }
		if (CmdFlags.getUseBV())
			return "(bvmul " + getChild(0).smtEncodeBV(satModel) + " " + getChild(1).smtEncodeBV(satModel) + ")";

		return null;
	}

	@Override
	public String smtEncodeInt(SMT satModel) {
		if (numChildren() > 2) { CmdFlags.errorExit("too many children"); }
		if (CmdFlags.getUseNIA()) {
			return "(* " + getChild(0).smtEncodeInt(satModel) + " " + getChild(1).smtEncodeInt(satModel) + ")";
		}
		return null;
	}
}