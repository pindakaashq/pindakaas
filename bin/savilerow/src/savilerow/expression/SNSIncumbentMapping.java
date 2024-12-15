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

import savilerow.model.*;

// Represents the primary (non-auxiliary) variables for an SNS search, and the corresponding 
// incumbent variables. Contains two lists of decision variables of the same length. 

public class SNSIncumbentMapping extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    protected transient Model m;
    
    public SNSIncumbentMapping(Model _m,ASTNode l1, ASTNode l2) {
		super(l1,l2);
		m=_m;
	}
	
    public boolean hasModel() {
        return true;
    }
    public Model getModel() {
        return m;
    }
    public void setModel(Model _m) {
        m=_m;
    }
    
	public ASTNode copy()
	{
	    return new SNSIncumbentMapping(m, getChild(0), getChild(1));
	}
	
	public boolean typecheck(SymbolTable st) {
	    return getChild(0).typecheck(st) && getChild(1).typecheck(st);
	}
	
	public String toString() {
	    return "incumbentMapping ("+getChild(0)+","+getChild(1)+")\n";
	}
	
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("INCUMBENTMAPPING [");
        getChild(0).toMinion(b, false);
        b.append(",");
        getChild(1).toMinion(b, false);
        b.append("]\n");
    }
    
    //  Make a new aux variable (incumbentDisable) and set of reified equality constraints.
    public ASTNode makeIncumbentDisable() {
        ASTNode incumbentDisable=m.global_symbols.newAuxiliaryVariable(new BooleanDomainFull());
        ArrayList<ASTNode> a=new ArrayList<ASTNode>();
        for(int i=1; i<getChild(0).numChildren(); i++) {
            a.add(new Implies(incumbentDisable, new Equals(getChild(0).getChild(i), getChild(1).getChild(i))));
        }
        assert m.sns.getChild(2) instanceof NoValue;
        m.sns.setChild(2, incumbentDisable);  //  Replace the NoValue with the new aux variable. 
        return new And(a);
    }
}
