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

import savilerow.CmdFlags;
import savilerow.model.*;

public class Iff extends LogicBinOp
{
    public static final long serialVersionUID = 1L;
	public Iff(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public ASTNode copy()
	{
	    return new Iff(getChild(0), getChild(1));
	}
	public boolean isRelation(){return true;}
	public boolean strongProp() {
	    return getChild(0).strongProp() && getChild(1).strongProp();
	}
	
	public ASTNode simplify() {
	    // Both children constant
	    if(getChild(0).isConstant() && getChild(1).isConstant()) {
	        return new BooleanConstant(getChild(0).getValue()==getChild(1).getValue());
	    }
	    
	    // One child is a constant.
	    if(getChild(0).isConstant() && getChild(0).getValue()==1) {
	        getChild(1).setParent(null);
	        return getChild(1);
	    }
	    if(getChild(1).isConstant() && getChild(1).getValue()==1) {
	        getChild(0).setParent(null);
	        return getChild(0);
	    }
	    if(getChild(0).isConstant() && getChild(0).getValue()==0) {
	        getChild(1).setParent(null);
	        return new Negate(getChild(1));
	    }
	    if(getChild(1).isConstant() && getChild(1).getValue()==0) {
	        getChild(0).setParent(null);
	        return new Negate(getChild(0));
	    }
	    
	    if(getChild(0).equals(getChild(1))) {  // If symbolically equal, return true.
	        return new BooleanConstant(true);
	    }
	    
	    // If one side is the negation of the other, return false.  
	    // Prevents deletevars unifying  x<->not(x) and causing infinite recursion of replacing x with not(x). 
	    if(getChild(0) instanceof Negate && getChild(0).getChild(0).equals(getChild(1))) {
	        return new BooleanConstant(false);
	    }
	    if(getChild(1) instanceof Negate && getChild(1).getChild(0).equals(getChild(0))) {
	        return new BooleanConstant(false);
	    }
	    
	    return null;
	}
	
	//  If contained in a Negate, push the negation inside 
	@Override
	public boolean isNegatable() {
	    return true;
	}
	@Override
	public ASTNode negation() {
	    // If one child is an identifier, negate that one.
	    if(getChild(0) instanceof Identifier) return new Iff(new Negate(getChild(0)), getChild(1));
	    if(getChild(1) instanceof Identifier) return new Iff(getChild(0), new Negate(getChild(1)));
	    
	    // Try to negate a side that can have the negation pushed further in. 
	    if(getChild(0).isNegatable()) return new Iff(new Negate(getChild(0)), getChild(1));
	    return new Iff(getChild(0), new Negate(getChild(1)));
	}
	
	@Override
	public ASTNode normalise() {
	    if(getChild(0).hashCode()>getChild(1).hashCode()) {
	        detachChildren();
	        return new Iff(getChild(1), getChild(0));
	    }
	    return this;
	}
	@Override
	public ASTNode normaliseAlpha() {
	    if(getChild(0).toString().compareTo(getChild(1).toString())>0) {
	        detachChildren();
	        return new Iff(getChild(1), getChild(0));
	    }
	    return null;
	}
	@Override
	public boolean typecheck(SymbolTable st) {
	    for(ASTNode child :  getChildren()) {
	        if(!child.typecheck(st)) {
	            return false;
	        }
	        if(!child.isRelation()) {
	            System.out.println("ERROR: Iff contains non-Boolean expression: "+child);
	            return false;
	        }
	    }
	    for(int i=0; i<2; i++) {
	        if(getChild(i) instanceof Iff || getChild(i) instanceof Implies) {
	            CmdFlags.println("ERROR: Nested non-associative operators: "+this);
	            CmdFlags.println("ERROR: Add brackets to remove ambiguity.");
	            return false;
	        }
        }
	    return true;
	}
	
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    assert bool_context;
	    b.append("eq(");
	    getChild(0).toMinion(b, false);
	    b.append(", ");
	    getChild(1).toMinion(b, false);
	    b.append(")");
	}
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
	    b.append("constraint bool_eq(");
	    getChild(0).toFlatzinc(b, true);
	    b.append(",");
	    getChild(1).toFlatzinc(b, true);
	    b.append(");");
	}
	public void toMinizinc(StringBuilder b, boolean bool_context) {
	    b.append("(");
	    getChild(0).toMinizinc(b, true);
	    b.append("<->");
	    getChild(1).toMinizinc(b, true);
	    b.append(")");
	}
	
	//  Identical to Equals.
	public Long toSATLiteral(Sat satModel) {
	    if(getChild(0).isConstant()) {
	        return getChild(1).directEncode(satModel, getChild(0).getValue());
        }
        if(getChild(1).isConstant()) {
            return getChild(0).directEncode(satModel, getChild(1).getValue());
        }
        return null;
	}
	
	public void toSAT(Sat satModel) throws IOException
	{
	    long a=getChild(0).directEncode(satModel, 1);
	    long b=getChild(1).directEncode(satModel, 1);
	    satModel.addClause(-a, b);
	    satModel.addClause(a, -b);
	}
    
	public void toSATWithAuxVar(Sat satModel, long aux) throws IOException {
	    long a=getChild(0).directEncode(satModel, 1);
	    long b=getChild(1).directEncode(satModel, 1);
	    
	    // Opposite sign on aux compared to XOR
	    satModel.addClause(-a, -b, aux);
        satModel.addClause(-a, b, -aux);
        satModel.addClause(a, -b, -aux);
        satModel.addClause(a, b, aux);
	}

    @Override
    public boolean usesSMTEncoding() {

		return CmdFlags.getUseBV() || CmdFlags.getUseNIA() || CmdFlags.getUseLIA() || CmdFlags.getUseIDL();
    }

    public void toSMT(SMT satModel) throws IOException {
	    satModel.addSMTClause(smtEncodeBool(satModel));
    }

    public String smtEncodeBool(SMT satModel) {
	    String ch0 = getChild(0).smtEncodeBool(satModel);
	    String ch1 = getChild(1).smtEncodeBool(satModel);

	    return "(and (or (not " + ch0 + ") " + ch1 + ") (or " + ch0 + " (not " + ch1 + ")))";
    }

	@Override
	public String smtEncodeBV(SMT satModel) {

		return "(ite " + this.smtEncodeBool(satModel) + " " + SMT.toSMTBV(1) + " " + SMT.toSMTBV(0) + ")";
	}

	@Override
	public String smtEncodeInt(SMT satModel) {
		return "(ite " + smtEncodeBool(satModel) + " 1 0)";
	}

	public String toString() {
	    return "("+getChild(0)+" <-> "+getChild(1)+")";
	}

    public boolean childrenAreSymmetric() {
        return true;
    }
}
