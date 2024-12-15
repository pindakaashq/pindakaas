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


import java.io.BufferedWriter;
import java.io.IOException;

import savilerow.model.SymbolTable;

// Represents a neighbourhood for Structured Neighbourhood Search

// CHild 0 : name
// Child 1 : size variable name (identifier or matrixderef) 
// child 2 : activation variable (identifier or matrixderef)
// child 3 : group name
// child 4 : List of variables acted upon. 

public class SNSNeighbourhood extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public SNSNeighbourhood(ASTNode[] args) {
        super(args);
	}
	
	public ASTNode copy()
	{
	    return new SNSNeighbourhood(getChildrenArray());
	}
	
	public boolean typecheck(SymbolTable st) {
	    // Avoid the name (child 0) and the group name
	    return getChild(1).typecheck(st) && getChild(2).typecheck(st) && getChild(4).typecheck(st);
	}
	
	public ASTNode deactivate() {
	    // Assign the size variable to any value.
	    ASTNode a=new Equals(getChild(1), NumberConstant.make(getChild(1).getBounds().lower));
	    
	    // Assign the activation variable to false. This should cause any constraints defining
	    // the neighbourhood to disappear.
	    ASTNode b=new Iff(getChild(2), new BooleanConstant(false));
	    return new And(a,b);
	}
	
	//  Partial deactivation of the neighbourhood before unrolling quantifiers,
	//  to help efficiency of SR.  Just disable the neighbourhood constraints.
	public ASTNode deactivateEarly() {
	    return new Iff(getChild(2), new BooleanConstant(false));
	}
	
	public String toString() {
	    return "neighbourhood "+getChild(0)+": ("+getChild(1)+","+getChild(2)+","+getChild(3)+","+getChild(4)+")\n";
	}
	
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("NEIGHBOURHOOD ");
        getChild(0).toMinion(b, false);
        b.append("(");
        getChild(1).toMinion(b, false);
        b.append(", ");
        getChild(2).toMinion(b, false);
        b.append(", ");
        getChild(3).toMinion(b, false);
        b.append(", ");
        getChild(4).toMinion(b, false);
        b.append(")\n");
    }
}
