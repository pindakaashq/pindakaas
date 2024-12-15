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


import savilerow.model.SymbolTable;

public class Popcount extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
	public Popcount(ASTNode a)
	{
		super(a);
	}
	
	public ASTNode copy() {
	    return new Popcount(getChild(0));
	}
	
	public boolean toFlatten(boolean propagate) { return false; }
	public boolean isNumerical() {
        return true;
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        if(!getChild(0).typecheck(st))
	        return false;
        
        if(getChild(0).getCategory() >= ASTNode.Decision) {
            System.out.println("ERROR: Popcount may not contain decision variables:"+this);
            return false;
        }
        
        if(getChild(0).getDimension()>0) {
            System.out.println("ERROR: Popcount may not contain a matrix:"+this);
            return false;
        }
        
        return true;
    }
    
	public ASTNode simplify()	{
	    if(getChild(0).isConstant()) {
	        long value=getChild(0).getValue();
	        
	        return NumberConstant.make(Long.bitCount(value));
	    }
	    return null;
	}
	
	public Intpair getBounds() {
	    return new Intpair(0L, 64L);
	}
	public PairASTNode getBoundsAST() {
	    return new PairASTNode(NumberConstant.make(0), NumberConstant.make(64));
	}
	
	public String toString() {
	    return "popcount("+getChild(0)+")";
	}
}
