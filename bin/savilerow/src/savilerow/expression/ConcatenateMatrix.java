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

// Flatten the top two dimensions of a matrix into one norm-indexed dimension. 

public class ConcatenateMatrix extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public ConcatenateMatrix(ASTNode a) {
        super(a);
    }
    
    public ASTNode copy() {
        return new ConcatenateMatrix(getChild(0));
    }
    
    public boolean typecheck(SymbolTable st) {
        if(! getChild(0).typecheck(st)) return false;
        if(getChild(0).getDimension()<2) {
            System.out.println("ERROR: Expected 2-dimensional or greater matrix inside concatenate (flatten) function: "+this);
            return false;
        }
        return true;
	}
    
    public ASTNode simplify()
    {
        if(getChild(0) instanceof CompoundMatrix || getChild(0) instanceof EmptyMatrix) {
            getChild(0).detachChildren();  // Do not copy.
            ASTNode[] tmp=getChild(0).getChildrenArray(1);
            return new Cat(tmp);
        }
        if(getChild(0) instanceof Identifier && getChild(0).getCategory()==ASTNode.Constant) {
            ASTNode[] tmp=((Identifier)getChild(0)).getCM().getChildrenArray(1);
            return new Cat(tmp);
        }
        return null;
    }
    
    public int getDimension() {
        return getChild(0).getDimension()-1;
    }
    public boolean isRelation() {
        return getChild(0).isRelation();
    }
    
	public String toString()
	{
	    StringBuilder b=new StringBuilder();
	    b.append("flatten(1, ");
	    b.append(getChild(0));
	    b.append(")");
	    return b.toString();
	}
}
