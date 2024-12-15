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

// Becomes AllDifferent at first simplify pass. 

public class NotEqual extends BinOp {
    public static final long serialVersionUID = 1L;
    public NotEqual(ASTNode a, ASTNode b) {
        super(a,b);
    }
    
    public ASTNode copy() {
        return new NotEqual(getChild(0), getChild(1));
    }
    
    public boolean isRelation() { return true; }
    
    public boolean typecheck(SymbolTable st) {
        if(!super.typecheck(st)) {
            return false;
        }
        for(int i=0; i<2; i++) {
            if(getChild(i) instanceof Less || getChild(i) instanceof LessEqual || getChild(i) instanceof Equals || getChild(i) instanceof NotEqual) {
                CmdFlags.println("ERROR: Nested non-associative operators: "+this);
                CmdFlags.println("ERROR: Add brackets to remove ambiguity.");
                return false;
            }
        }
        return true;
    }
    
    public ASTNode simplify() {
        detachChildren();
        return new AllDifferent(getChild(0), getChild(1));
    }
    
    public String toString() {
        return "(" + getChild(0) + "!=" + getChild(1) + ")";
    }
}
