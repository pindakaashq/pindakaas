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

public class ComprehensionForall extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public ComprehensionForall(ASTNode i, ASTNode d) {
        super(i,d);
        assert i instanceof Identifier;
    }
    
	public ASTNode copy()
	{
	    return new ComprehensionForall(getChild(0), getChild(1));
	}
	
	public String toString() {
	    return getChild(0)+" : "+getChild(1);
	}
	
	public boolean typecheck(SymbolTable st) {
	    if(!(getChild(0) instanceof Identifier)) {
	        System.out.println("ERROR: Comprehension variable does not have proper name: "+this);
	        return false;
	    }
	    
	    if(!getChild(1).typecheck(st)) {
	        return false;
	    }
	    
	    if(getChild(1).getCategory()>ASTNode.Quantifier) {
	        System.out.println("ERROR: In comprehension generator: "+this); 
            System.out.println("ERROR: Decision variable in quantifier domain.");
            return false;
	    }
	    
	    if(! ( getChild(1) instanceof MatrixDomain || getChild(1).isFiniteSet()))  {
            System.out.println("ERROR: In comprehension generator: "+this); 
            System.out.println("ERROR: Expected finite domain or matrix domain.");
            return false;
        }
        
        if(getChild(1) instanceof MatrixDomain) {
            if(((MatrixDomain)getChild(1)).nesting()>1) {
                System.out.println("ERROR: matrix indexed by matrix not allowed in comprehension generator: "+this);
                return false;
            }
        }
        
	    return true;
	}
	
	@Override
	public ASTNode getDomainForId(ASTNode id) {
	    if(getChild(0).equals(id)) {
	        return getChild(1);
	    }
	    else {
	        return getParent().getDomainForId(id);
	    }
    }
}
