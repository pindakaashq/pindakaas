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

/* =============================================================================
 Base class for the matrix binary operators 
 Just exists to replace typecheck.
==============================================================================*/

abstract public class MatrixBinOp extends BinOp
{
    public static final long serialVersionUID = 1L;
    public MatrixBinOp(ASTNode l, ASTNode r)
	{
		super(l,r);
	}
	
	@Override
	public boolean typecheck(SymbolTable st) {
	    if(!getChild(0).typecheck(st) || !getChild(1).typecheck(st)) {
	        return false;
	    }
	    if(getChild(0).getDimension()!=1) {
	        CmdFlags.println("ERROR: Expected one-dimensional matrix in expression: "+this);
	        CmdFlags.println("ERROR: found: "+getChild(0));
	        return false;
	    }
	    if(getChild(1).getDimension()!=1) {
	        CmdFlags.println("ERROR: Expected one-dimensional matrix in expression: "+this);
	        CmdFlags.println("ERROR: found: "+getChild(1));
	        return false;
	    }
	    return true;
	}
}