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

import savilerow.CmdFlags;
import savilerow.model.*;

public class UnaryMinus extends Unary
{
    public static final long serialVersionUID = 1L;
    public UnaryMinus(ASTNode a)
    {
        super(a);
    }
    
	public ASTNode copy()
	{
	    return new UnaryMinus(getChild(0));
	}
	
	public ASTNode simplify() {
	    if(getChild(0) instanceof UnaryMinus) {
	        getChild(0).getChild(0).setParent(null);
	        return getChild(0).getChild(0);
	    }
	    if(getChild(0).isConstant()) {
	        return NumberConstant.make(-getChild(0).getValue());
	    }
	    
	    // Push it inside numerical types. 
	    if(getChild(0) instanceof WeightedSum) {
	        long[] w=((WeightedSum)getChild(0)).getWeightsArray();
	        for(int i=0; i<w.length; i++) w[i]=-w[i];
	        getChild(0).detachChildren();
	        return new WeightedSum(getChild(0).getChildrenArray(), w);
	    }
	    if(getChild(0) instanceof Times) {
	        getChild(0).detachChildren();
	        ASTNode[] a=getChild(0).getChildrenArray();
	        a[0]=new UnaryMinus(a[0]);  // Negate first element. 
	        return new Times(a);
	    }
	    
	    // Can't do Div and Mod because the floor(l/r) semantics don't allow it. 
	    //if(getChild(0) instanceof Divide) {
	    //    return new Divide(new UnaryMinus(getChild(0).getChild(0)), getChild(0).getChild(1));
	    //}
	    
	    // Also push inside Max and Min
	    if(getChild(0) instanceof Max || getChild(0) instanceof Min) {
	        // Negate everything inside and return Max for a Min and vice versa. 
	        getChild(0).detachChildren();
	        ASTNode[] a=getChild(0).getChildrenArray();
	        for(int i=0; i<a.length; i++) a[i]=new UnaryMinus(a[i]);
	        if(getChild(0) instanceof Max) {
	            return new Min(a);
	        }
	        else {
	            return new Max(a);
	        }
	    }
	    
	    return null;
	}
    @Override
    public int polarity(int child) {
        return -polarity();
    }
    
	@Override
	public boolean typecheck(SymbolTable st) {
	    if(!getChild(0).typecheck(st)) return false;
        if(getChild(0).getDimension()>0) {
            CmdFlags.println("ERROR: Unexpected matrix in unary minus: "+this);
            return false;
        }
        if(getChild(0).isSet()) {
            CmdFlags.println("ERROR: Unexpected set in unary minus: "+this);
            return false;
        }
        return true;
    }
	
	public boolean toFlatten(boolean propagate) { return true;}
	public boolean isNumerical() {
        return true;
    }
    
    public void toMinionWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException
	{
	    b.append("minuseq(");
	    aux.toMinion(b, false);
	    b.append(", ");
	    getChild(0).toMinion(b, false);
	    b.append(")");
	}
	
	public void toFlatzincWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException {
	    b.append("constraint int_lin_eq([-1,-1],[");
	    getChild(0).toFlatzinc(b, false);
	    b.append(",");
	    aux.toFlatzinc(b, false);
	    b.append("],0);");
	}
	
	public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("(-");
        getChild(0).toMinizinc(b, false);
        b.append(")");
    }
    
	public String toString()
	{
	    return "(-"+getChild(0)+")";
	}
	
    public boolean usesSMTEncoding() {
        return CmdFlags.getUseNIA() ||  CmdFlags.getUseBV() || CmdFlags.getUseLIA();
    }

    public String smtEncodeInt(SMT satModel) {
        return "(- " + getChild(0).smtEncodeInt(satModel) + ")";
    }

	public String smtEncodeBV(SMT satModel) {
		return "(bvneg " + getChild(0).smtEncodeBV(satModel) + ")";
	}
	
	public Intpair getBounds() {
	    Intpair a=getChild(0).getBounds();
	    long tmp;
	    if(a.lower==Long.MIN_VALUE) {
	        tmp=Long.MAX_VALUE;
	    }
	    else {
	        tmp=-a.lower;
	    }
	    
	    if(a.upper==Long.MAX_VALUE) {
	        a.lower=Long.MIN_VALUE;
	    }
	    else {
	        a.lower=-a.upper;
	    }
	    
	    a.upper=tmp;
	    return a;
	}
	public ArrayList<Intpair> getIntervalSetExp() {
	    return Intpair.multIntervalSet(getChild(0).getIntervalSetExp(), -1);
	}
	
	public void toSATWithAuxVar(Sat satModel, ASTNode auxVar) throws IOException {
        satModel.supportEncodingBinary(this, getChild(0), auxVar);
	}
	@Override
	public boolean test(long val1, long val2) {
	    return val1==-val2;
	}
    
    public void toMIP(BufferedWriter b) throws IOException {
        b.append(" - ");
        b.append(getChild(0).toString());
    }
}
