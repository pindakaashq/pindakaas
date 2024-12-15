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
import java.util.ArrayList;

import savilerow.model.SymbolTable;

// A container with the incumbent mapping, neighbourhoods, incumbent disable, variable groups.

public class SNS extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public SNS(ASTNode incmap, ASTNode hoods, ASTNode incdes, ASTNode groups) {
		super(incmap, hoods, incdes, groups);
	}
	
	public ASTNode copy() {
	    return new SNS(getChild(0), getChild(1), getChild(2), getChild(3));
	}
	
	public boolean typecheck(SymbolTable st) {
	    return getChild(0).typecheck(st) && getChild(1).typecheck(st) && getChild(2).typecheck(st) && getChild(3).typecheck(st);
	}
	
	public ASTNode deactivate() {
	    ArrayList<ASTNode> newcons=new ArrayList<ASTNode>();
	    // Switch off all neighbourhoods
	    for(int i=0; i<getChild(1).numChildren(); i++) {
	        newcons.add( ((SNSNeighbourhood) getChild(1).getChild(i)).deactivate());
	    }
	    
	    // Disable the incumbent variables -- they will be unified with the primary variables.
	    newcons.add(new Iff(getChild(2), new BooleanConstant(true)));
	    
	    return new And(newcons);
	}
	
	//  Set neighbourhood activation vars to false early to avoid unrolling overhead.
	public ASTNode deactivateEarly() {
	    ArrayList<ASTNode> newcons=new ArrayList<ASTNode>();
	    // Switch off all neighbourhoods
	    for(int i=0; i<getChild(1).numChildren(); i++) {
	        newcons.add( ((SNSNeighbourhood) getChild(1).getChild(i)).deactivateEarly());
	    }
	    return new And(newcons);
	}
	
	public String toString() {
	    return getChild(0).toString()+getChild(1).toString()+getChild(2).toString()+getChild(3).toString();
	}
	
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
	    b.append("**NEIGHBOURHOODS**\n");
        b.append("INCUMBENTDISABLE ");
        getChild(2).toMinion(b, false);
        b.append("\n");
        
        // Incumbent mapping
        getChild(0).toMinion(b, false);
        
        // Groups
        for(int i=0; i<getChild(3).numChildren(); i++) {
            getChild(3).getChild(i).toMinion(b, false);
        }
        
        // Neighbourhoods
        for(int i=0; i<getChild(1).numChildren(); i++) {
            getChild(1).getChild(i).toMinion(b, false);
        }
    }
}
