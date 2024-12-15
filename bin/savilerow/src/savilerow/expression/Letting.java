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

// Represents a Letting statement
// May have a third child that is the domain, mainly useful for matrices of constants
// to store the matrix index dimensions.

public class Letting extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public Letting(ASTNode l, ASTNode r)
	{
		super(l,r);
	}
	
	public Letting(ASTNode l, ASTNode r, ASTNode dom)
	{
	    super(l,r,dom);
	}
	public boolean typecheck(SymbolTable st) {
	    if(numChildren()>2) {
	        return getChild(1).typecheck(st) && getChild(2).typecheck(st);
	    }
	    else {
	        return getChild(1).typecheck(st);
	    }
	}
	
	public ASTNode copy()
	{
	    if(numChildren()==2)
	        return new Letting(getChild(0), getChild(1));
	    else
	        return new Letting(getChild(0), getChild(1), getChild(2));
	}
	public String toString() {
	    String st="letting "+getChild(0).toString()+" ";
	    if(numChildren()==3) {
	        st=st+":"+getChild(2)+" ";
	    }
	    return st+"be "+getChild(1);
	}
}

