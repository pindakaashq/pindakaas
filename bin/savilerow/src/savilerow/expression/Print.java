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

public class Print extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    
    public Print(ASTNode a) {
        super(a);
    }
    
    public boolean isRelation() {
        return true;
    }
    public ASTNode copy() {
        return new Print(getChild(0));
    }
    public boolean toFlatten(boolean propagate) { return false; }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        return getChild(0).typecheck(st);
	}
    
	//  When it contains a constant, print out the constant and this expression becomes true.
	public ASTNode simplify() {
	    if(getChild(0).getCategory()==ASTNode.Constant) {
	        ASTNode val=getChildConst(0);
	        System.out.println("PRINT: "+val);
	        return new BooleanConstant(true);
	    }
	    return null;
	}
}
