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

import savilerow.model.SymbolTable;

// Takes any matrix expression and finds the first index of it.
// Similar to Indices.  Works for both regular and irregular matrices.

public class IndexOf extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
	public IndexOf(ASTNode a)
	{
		super(a);
	}
	
	public ASTNode copy() {
	    return new IndexOf(getChild(0));
	}
	
	public boolean toFlatten(boolean propagate) { return false; }
	public boolean isNumerical() {
        return false;
    }
    public boolean isRelation() {
        return false;
    }
    public boolean isSet() {
        return true;
    }
    public boolean isFiniteSet() {
        return true;
    }
    public boolean isFiniteSetUpper() {
        return true;
    }
    public boolean isFiniteSetLower() {
        return true;
    }
    @Override
    public int getCategory() {
        //  indexOf cannot be a decision expression. The 'highest' possible type of expression is Quantifier. 
        return ASTNode.Quantifier;
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        if(!getChild(0).typecheck(st)) {
	        return false;
	    }
        
        if(getChild(0).getDimension()==0) {
            System.out.println("ERROR: indexOf must contain a matrix:"+this);    // Why must it contain a matrix? Perhaps should also work on scalars. 
            return false;
        }
        
        return true;
    }
    
	public ASTNode simplify() {
	    ArrayList<ASTNode> idxdoms=getChild(0).getIndexDomains();
	    if(idxdoms==null) {
	        // Can't evaluate this yet. 
	        return null;
	    }
	    return idxdoms.get(0);
	}
	
	public Intpair getBounds() {
	    return new Intpair(Long.MIN_VALUE, Long.MAX_VALUE);   // Delay.
	}
	public PairASTNode getBoundsAST() {
	    return new PairASTNode(new NegInfinity(), new PosInfinity()); // Delay.
	}
    
	public String toString() {
	    return "indexOf("+getChild(0)+")";
	}
}
