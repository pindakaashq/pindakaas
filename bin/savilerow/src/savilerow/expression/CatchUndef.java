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

import savilerow.CmdFlags;
import savilerow.model.SymbolTable;

public class CatchUndef extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    
    public CatchUndef(ASTNode exp, ASTNode defaultval) {
        super(exp,defaultval);
    }
    
	public ASTNode copy() {
	    return new CatchUndef(getChild(0), getChild(1));
	}
	
	public boolean isRelation() {
	    return getChild(0).isRelation();
	}
	public boolean isNumerical() {
	    return getChild(0).isNumerical();
    }
    public boolean isSet() {
        return getChild(0).isSet();
    }
    
    public boolean toFlatten(boolean propagate) {
        return false;
    }
    
	public Intpair getBounds()
	{
	    return getChild(0).getBounds();
	}
	
	public boolean typecheck(SymbolTable st) {
	    for(int i=0; i<numChildren(); i++) {
	        if(! getChild(i).typecheck(st)) return false;
	    }
	    // scalars
	    if(getChild(0).getDimension()>0 || getChild(1).getDimension()>0) {
	        CmdFlags.println("ERROR: Unexpected matrix in catchUndef function: " + this);
	        return false;
	    }
	    if(getChild(0).isNumerical() != getChild(1).isNumerical()) {
	        CmdFlags.println("ERROR: Types do not match in catchUndef function: " + this);
	        return false;
	    }
	    if(getChild(1).getCategory()!=ASTNode.Constant) {
	        CmdFlags.println("ERROR: catchUndef must have a constant as the second argument: "+this);
	        return false;
	    }
	    //  Check value is same type as expression
	    return true;
	}
	
	public String toString() {
	    return "catchUndef("+getChild(0)+", "+getChild(1)+")";
	}
	
	//  Special method to generate the replacement expression when an undefined condition is found
	public ASTNode replacementExp(ASTNode definedCons) {
	    //  [getChild(1), getChild(0); int(0..1)][definedCons]   i.e. use definedCons as a 
	    //  switch to choose the expression when it is defined, the default val otherwise.
	    ArrayList<ASTNode> cm=new ArrayList<ASTNode>();
	    cm.add(getChild(1)); cm.add(getChild(0));
	    ArrayList<ASTNode> idx=new ArrayList<ASTNode>();
	    idx.add(definedCons);
	    ASTNode idxdom=new IntegerDomainConcrete(0,1);
	    ASTNode newexp = new SafeMatrixDeref(new CompoundMatrix(idxdom, cm), idx);
	    
	    //  getChild(0) may contain more than one potential source of undef,
	    //  so wrap again with catchUndef
	    return new CatchUndef(newexp, getChild(1));
	}
}
