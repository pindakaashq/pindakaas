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


import savilerow.CmdFlags;
import savilerow.model.SymbolTable;

// Represents a Given statement

public class Given extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public Given(ASTNode l, ASTNode r)
    {
        super(l,r);
    }
    
    public ASTNode copy()
    {
        return new Given(getChild(0), getChild(1));
    }
    
    public boolean typecheck(SymbolTable st) {
        // Tricky here -- if right child is a matrix domain it may contain
        // undefined identifiers in indexed by [int(1..p).....
        
        // Left child has to be an identifier
        if(!(getChild(0) instanceof Identifier) || st.hasVariable(getChild(0).toString())) {
            CmdFlags.println("ERROR: Left side of given must be an undefined identifier: "+this);
            return false;
        }
        
        if(getChild(1) instanceof MatrixDomain) {
            if(getChild(1).getCategory()!=ASTNode.Undeclared) {
                if(!((MatrixDomain)getChild(1)).typecheck(st)) {
                    return false;
                }
            }
            else {
                //  Contains undeclared identifiers
                if(!((MatrixDomain)getChild(1)).typecheck_in_given(st)) {
                    return false;
                }
            }
            
            if(((MatrixDomain)getChild(1)).nesting()>1) {
                CmdFlags.println("ERROR: Matrix indexed by matrix not allowed in given: "+this);
                return false;
            }
            return true;
        }
        else {
            return getChild(1).typecheck(st);
        }
    }
    
    public String toString() {
        return "given "+getChild(0)+" : "+getChild(1);
    }
}




