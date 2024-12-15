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

// Represents a group of variables for SNS search. 

public class SNSGroup extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public SNSGroup(ASTNode name, ASTNode vars) {
		super(name,vars);
	}
	
	public ASTNode copy()
	{
	    return new SNSGroup(getChild(0), getChild(1));
	}
	
	public boolean typecheck(SymbolTable st) {
	    return getChild(1).typecheck(st);
	}
	
	public String toString() {
	    return "SNSGroup "+getChild(0)+" : "+getChild(1)+"\n";
	}
	
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("GROUP ");
        getChild(0).toMinion(b, false);
        b.append("(");
        getChild(1).toMinion(b, false);
        b.append(")\n");
    }
}
