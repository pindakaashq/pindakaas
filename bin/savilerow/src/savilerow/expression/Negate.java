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

// boolean negation.

public class Negate extends Unary
{
    public static final long serialVersionUID = 1L;
    public Negate(ASTNode a)
    {
        super(a);
    }
    
	public ASTNode copy()
	{
	    return new Negate(getChild(0));
	}
	public boolean isRelation(){return true;}
	public boolean strongProp() {
        return getChild(0).strongProp();
    }
	
	public ASTNode simplify() {
	    if(getChild(0).isConstant()) {
	        if(getChild(0).getValue()==0) return new BooleanConstant(true);
	        else return new BooleanConstant(false);
	    }
	    
	    // Negate expressions that define isNegatable and negation methods. 
	    if(getChild(0).isNegatable()) {
            return getChild(0).negation();
        }
        
	    return null;
	}
	
	@Override
	public boolean isNegatable() {
	    return true;
	}
	@Override
	public ASTNode negation() {
	    return getChild(0);
	}
	
	@Override
    public int polarity(int child) {
        return -polarity();
    }
	
	//  Improve flattening when the solver or context allows negation.
	@Override
	public boolean toFlatten(boolean propagate) {
	    if( (CmdFlags.getMiniontrans() || CmdFlags.getSattrans()) && getChild(0) instanceof Identifier) {
	        return false;
	    }
	    if( (CmdFlags.getFlatzinctrans() || CmdFlags.getMinizinctrans()) && getParent() instanceof Implies) {
	        return CmdFlags.getOrtoolstrans();      // Only extract negation within implies if the back-end is Or-Tools (no bool_clause constraint available)
	    }
	    return super.toFlatten(propagate);
	}
	
	public boolean typecheck(SymbolTable st) {
	    if(!getChild(0).typecheck(st))
	        return false;
        if(!getChild(0).isRelation()) {
            System.out.println("ERROR: Boolean negation contains numerical expression:"+this);
            return false;
        }
	    return true;
	}
	
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
	    if(bool_context) {
	        // Parent expects a constraint. 
	        b.append("w-literal(");
            getChild(0).toMinion(b, false);
            b.append(",0)");
	    }
	    else {
	        // Use Minion's negation mapper. 
	        b.append("!");
	        getChild(0).toMinion(b, false);
	    }
	}
	
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
	    b.append("constraint bool_eq(");
	    getChild(0).toFlatzinc(b, true);
	    b.append(",false);");
	}
	
	public String toString()
	{
	    return "(!"+getChild(0)+")";
	}
	public void toMinizinc(StringBuilder b, boolean bool_context) {
	    b.append("(not ");
	    getChild(0).toMinizinc(b, true);
	    b.append(")");
	}
	
	public Long toSATLiteral(Sat satModel) {
        if(getChild(0) instanceof SATLiteral) {
            return -((SATLiteral)getChild(0)).getLit();
        }
        else return null;
    }
	public void toSAT(Sat satModel) throws IOException
	{
		getChild(0).toSATWithAuxVar(satModel, -satModel.getTrue());   //  Pass false for the aux var to negate the child constraint.
	}
	
	public void toSATWithAuxVar(Sat satModel, long auxVarValue) throws IOException {
		getChild(0).toSATWithAuxVar(satModel,-auxVarValue);
	}

	// SMT
	public boolean usesSMTEncoding() { return CmdFlags.getUseBV() || CmdFlags.getUseNIA() || CmdFlags.getUseLIA(); }

    public void toSMT(SMT satModel) throws IOException {
        satModel.addSMTClause(smtEncodeBool(satModel));
    }

    public String smtEncodeBool(SMT satModel) {
        return "(not " + getChild(0).smtEncodeBool(satModel) + ")";
    }

	@Override
	public String smtEncodeBV(SMT satModel) {
		return "(ite " + this.smtEncodeBool(satModel) + " " + SMT.toSMTBV(1) + " " + SMT.toSMTBV(0) + ")";
	}

	@Override
	public String smtEncodeInt(SMT satModel) {
		return "(ite " + smtEncodeBool(satModel) + " 1 0)";
	}
}
