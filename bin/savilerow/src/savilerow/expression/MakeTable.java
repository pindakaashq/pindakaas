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

// Turn an expression into some other representation, e.g. a shorttable constraint. 

public class MakeTable extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public MakeTable(ASTNode a)
    {
        super(a);
    }
    
    public ASTNode copy()
    {
        return new MakeTable(getChild(0));
    }
    
    public boolean toFlatten() { return false; }
    public boolean isRelation() { return true; }
    public boolean strongProp() {
        return true;
    }
    
    public ASTNode simplify() {
        if(getChild(0).isConstant()) {
            getChild(0).setParent(null);
            return getChild(0);
        }
        return null;
    }
    
    public boolean typecheck(SymbolTable st) {
        if(!(getChild(0).typecheck(st))) return false;
        if(! getChild(0).isRelation() || getChild(0).getDimension()>0) {
            CmdFlags.println("ERROR: makeTable may only contain boolean expressions: "+this);
            return false;
        }
        return true;
    }
    
    public String toString() {
        return "makeTable("+getChild(0)+")";
    }
}