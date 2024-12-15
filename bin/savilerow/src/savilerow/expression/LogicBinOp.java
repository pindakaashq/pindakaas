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
 Base class for the logical binary operators e.g. Iff
 Just exists to replace typecheck.
==============================================================================*/

abstract public class LogicBinOp extends BinOp
{
    public static final long serialVersionUID = 1L;
    public LogicBinOp(ASTNode l, ASTNode r)
	{
		super(l,r);
	}
	
	public boolean typecheck(SymbolTable st) {
	    for(int i=0; i<2; i++) {
	        if(!getChild(i).typecheck(st)) return false;
	        if(getChild(i).getDimension()>0) {
	            CmdFlags.println("ERROR: Unexpected matrix in binary logical operator: "+this);
	            return false;
	        }
	        if(getChild(i).isSet()) {
	            CmdFlags.println("ERROR: Unexpected integer set in binary logical operator: "+this);
	            return false;
	        }
	        if(!getChild(i).isRelation()) {
	            CmdFlags.println("ERROR: Unexpected non-boolean expression in binary logical operator: "+this);
	            return false;
	        }
        }
        return true;
    }
}