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

import savilerow.CmdFlags;

//  Refers to a variable or matrix defined by a find statement.
//  Special type that is used only to refer to 
//  variables/matrices from previously found solutions.

public class FromSolution extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public String name;
    
	public FromSolution(ASTNode a) {
	    super(a);
	    name=a.toString();
	}
	
	private FromSolution(ASTNode a, String n) {
	    super(a);
	    name=n;
	}
	
	public ASTNode copy() {
	    return new FromSolution(getChild(0), name);
	}
	public ASTNode simplify() {
	    //  Check above for DominanceRelation
	    ASTNode p=getParent();
	    while(p!=null) {
	        if(p instanceof DominanceRelation) {
	            return null;
	        }
	        p=p.getParent();
	    }
	    CmdFlags.warning("fromSolution function found outside DominanceRelation.");
	    return getChild(0);  // Strip off the FromSolution function, we are outside DominanceRelation.
	}
	
	public boolean isRelation() {
	    return getChild(0).isRelation();
	}
	public boolean isNumerical() {
	    return getChild(0).isNumerical();
	}
	public int getDimension() {
	    return getChild(0).getDimension();
    }
    public int getCategory() {
        return getChild(0).getCategory();
    }
    public Intpair getBounds() {
        return getChild(0).getBounds();
    }
    public ArrayList<Intpair> getIntervalSetExp() {
        return getChild(0).getIntervalSetExp();
    }
    public ArrayList<ASTNode> getIndexDomains() {
        return getChild(0).getIndexDomains();
    }
    //  equals and hashcode....?
	
	public String toString() {
	    return "fromSolution("+name+")";
	}
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        getChild(0).toMinion(b, bool_context);
    }
}
