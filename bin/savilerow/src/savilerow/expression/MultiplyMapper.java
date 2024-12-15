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


import java.io.IOException;
import java.util.ArrayList;

import savilerow.CmdFlags;
import savilerow.model.*;

public class MultiplyMapper extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
	public MultiplyMapper(ASTNode a, ASTNode mult) {
	    super(a, mult);
	}
	
	public ASTNode copy()
	{
	    return new MultiplyMapper(getChild(0), getChild(1));
	}
	
	public boolean toFlatten(boolean propagate) { return false;}  // Never flatten this. 
	public boolean strongProp() {
        return getChild(0).strongProp();
    }
    public ASTNode simplify() {
        assert getChild(0).getCategory()<=ASTNode.Decision || getChild(0).getCategory()==ASTNode.Undeclared;  // allows it to work on detached bits of trees.
        assert getChild(1).getCategory()<=ASTNode.Quantifier || getChild(1).getCategory()==ASTNode.Undeclared;
        
        if(getChild(0).isConstant()) {
            detachChildren();
            return new Times(getChild(0), getChild(1));
        }
        
        if(getChild(1).equals(NumberConstant.make(1))) {
            getChild(0).setParent(null);
            return getChild(0);
        }
        if(getChild(1).equals(NumberConstant.make(0))) {
            return NumberConstant.make(0);
        }
        // Unflattening simplify.
        //if (getChild(1).equals(NumberConstant.make(-1))) {
        //    return new UnaryMinus(getChild(0));
        //}
        
        if(getChild(0) instanceof MultiplyMapper) {
            // Put the two multiplymappers together.
            getChild(0).detachChildren();
            getChild(1).setParent(null);
            ASTNode newmul=BinOp.makeBinOp("*", getChild(1), getChild(0).getChild(1));
            return new MultiplyMapper(getChild(0).getChild(0), newmul);
        }
        return null;
    }
    @Override
	public int polarity(int child) {
	    return polarity()*(getChild(1).getValue()>0 ? 1 : -1 );
	}
	
	public Intpair getBounds()
	{
	    Intpair a=getChild(0).getBounds();
	    for(int i=1; i<numChildren(); i++) {
            Intpair b=getChild(i).getBounds();
            // multiply the four combinations of bounds
            long w=Times.multiply(a.lower, b.lower);
            long x=Times.multiply(a.upper, b.lower);
            long y=Times.multiply(a.lower, b.upper);
            long z=Times.multiply(a.upper, b.upper);
            a.lower=Math.min(w, Math.min(x, Math.min(y,z)));
            a.upper=Math.max(w, Math.max(x, Math.max(y,z)));
	    }
	    return a;
	}
	
	public ArrayList<Intpair> getIntervalSetExp() {
        ArrayList<Intpair> l = getChild(0).getIntervalSetExp();
        long factor=getChild(1).getValue();
        return Intpair.multIntervalSet(l, factor);
    }
    
	public String toString() {
	    return "mult("+getChild(0)+", "+getChild(1)+")";
	}
	
	////////////////////////////////////////////////////////////////////////////
	//  SAT encoding -- same interface as Identifier
	public boolean hasLiteralEncoding() {
        return true;
    }
	public long directEncode(Sat satModel, long value) {
	    long m=getChild(1).getValue();
	    if(value%m != 0) {
	        return -satModel.getTrue();   // Non-integer value of division --false. 
	    }
	    return getChild(0).directEncode(satModel, value/m);
    }
    public long orderEncode(Sat satModel, long value) {
        long m=getChild(1).getValue();
        if(m>0) {
            //  Just divide rounding towards -inf.
            return getChild(0).orderEncode(satModel, Divide.div(value,m));
        }
        else {
            //  Divide rounding up.  -5x <= 7,  5x >= -7, x >= -1 (round up), !(x < -1), !(x <= -2)  (subtract 1)
            long q=Divide.divceil(value, m);
            return -getChild(0).orderEncode(satModel, q-1);
        }
    }

    ////////////////////////////////////////////////////////////////////////////
    //  SMT encoding
    public boolean usesSMTEncoding() {
        return CmdFlags.getUseBV() || CmdFlags.getUseNIA() || CmdFlags.getUseLIA() || (CmdFlags.getUseIDL() && canVariableEncode());
    }

    public boolean canVariableEncode() {
        return CmdFlags.getUseAuxSMT() && getChild(0) instanceof Identifier;
    }

    public String smtEncodeInt(SMT satModel) {
	    if (CmdFlags.getUseLIA() || CmdFlags.getUseNIA()) {
	        if(getChild(1).getValue()==-1) {
	            return "(- " + getChild(0).smtEncodeInt(satModel) + ")";  // Unary negation
	        }
	        else {
	            return "(* " + getChild(0).smtEncodeInt(satModel) + " " + getChild(1).smtEncodeInt(satModel) + ")";
	        }
        }
	    else if (CmdFlags.getUseIDL() && canVariableEncode()) {
	        try {
                return satModel.createAuxSMTVariableFor(getChild(0), getChild(1).getValue());
            } catch (IOException e) {
                CmdFlags.errorExit("Could not create auxiliary variable for the node " + toString() + " because output file could not be accessed");
            }
        }

	    CmdFlags.errorExit("Can't encode Int for MultiplyMapper");
	    return null;
    }

    @Override
    public String smtEncodeBV(SMT satModel) {
	    if (numChildren() > 2) { CmdFlags.errorExit("too many children"); }
        if (CmdFlags.getUseBV()) {
            if(getChild(1).getValue()==-1) {
                return "(bvneg " + getChild(0).smtEncodeBV(satModel) + ")";
            }
            else {
                return "(bvmul " + getChild(0).smtEncodeBV(satModel) + " " + getChild(1).smtEncodeBV(satModel) + ")";
            }
        }
        
        return null;
    }
}
