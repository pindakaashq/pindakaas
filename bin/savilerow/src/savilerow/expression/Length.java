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

// Takes a one-dimensional matrix and evaluates to the number of elements of that
// matrix. 

public class Length extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
	public Length(ASTNode a)
	{
		super(a);
	}
	
	public ASTNode copy() {
	    return new Length(getChild(0));
	}
	
	public boolean toFlatten(boolean propagate) { return false; }
	public boolean isNumerical() {
        return true;
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        if(!getChild(0).typecheck(st))
	        return false;
        
        if(getChild(0).getDimension()!=1) {
            System.out.println("ERROR: Length must contain a one-dimensional matrix:"+this); 
            return false;
        }
        
        return true;
    }
    
    public Intpair getBounds() {
        return new Intpair(0L, Long.MAX_VALUE);
    }
    public PairASTNode getBoundsAST() {
	    return new PairASTNode(NumberConstant.make(0), new PosInfinity());	    
	}
	
	public ASTNode simplify() {
	    ArrayList<ASTNode> idxdoms=getChild(0).getIndexDomains();
	    
	    if(idxdoms==null) {
	        // Can't evaluate this yet. 
	        return null;
	    }
	    
	    assert idxdoms.size()==1;
	    
	    ArrayList<Intpair> intervals=idxdoms.get(0).getIntervalSet();
	    long numvals=Intpair.numValues(intervals);
	    
	    return NumberConstant.make(numvals);
	}
	
	public String toString() {
	    return "length("+getChild(0)+")";
	}
}
