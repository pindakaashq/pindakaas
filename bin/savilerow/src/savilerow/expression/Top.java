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

import savilerow.CmdFlags;
import savilerow.model.*;

// The top of the AST for constraints. Usually contains an And. 

public class Top extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public Top(ASTNode in) {
        super(in);
    }
    
	public ASTNode copy() {
	    return new Top(getChild(0));
	}
	
	public String toString() { return getChild(0).toString(); }
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException { 
	    getChild(0).toFlatzinc(b, true);
	    b.append("\n");
	}
	@Override
	public int polarity(int child) {
	    return 1;
	}
	public void toMinizinc(StringBuilder b, boolean context) {
	    if(getChild(0) instanceof And) {
	        getChild(0).toMinizinc(b, context);
	    }
	    else {
	        b.append("constraint ");
	        getChild(0).toMinizinc(b, context);
	        b.append(";\n");
	    }
	}
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
	    assert bool_context;
	    getChild(0).toMinion(b, true);
	}
	public void toSAT(Sat satModel) throws IOException {
	    if(getChild(0) instanceof BooleanConstant) {
	        if(getChild(0).getValue()==1) {
	            // output nothing  --  formula is trivially satisfiable.
	        }
	        else {
	            // make an unsatisfiable formula by using the true var.
	            satModel.addClause(-satModel.getTrue());
	        }
	    }
	    else {
	        if(! (getChild(0) instanceof And)) {
	            satModel.addComment(String.valueOf(getChild(0)).replaceAll("\n", " "));
	        }
	        getChild(0).toSAT(satModel);
	    }
	}
	public void toSMT(SMT satModel) throws IOException {
        if(getChild(0) instanceof BooleanConstant) {
            if(getChild(0).getValue()==1) {
                // output nothing  --  formula is trivially satisfiable.
            }
            else {
                // make an unsatisfiable formula by using the true var.
                satModel.addClause(-satModel.getTrue());
            }
        }
        else {
            if(! (getChild(0) instanceof And)) {
                satModel.addComment(String.valueOf(getChild(0)).replaceAll("\n", " "));
            }
            getChild(0).toSMT(satModel);
        }
    }
    public void toMIP(BufferedWriter b) throws IOException {
        getChild(0).toMIP(b);
    }
    
    public boolean usesSMTEncoding() {

    	return CmdFlags.getUseNIA() || CmdFlags.getUseLIA() || CmdFlags.getUseIDL() || CmdFlags.getUseBV();
    }
    public boolean willSMTEncode() {
        return usesSMTEncoding();
    }
	public boolean inTopConjunction() { return true; }
	public boolean inTopAnd() { return true; }
	
	public boolean isRelation() { return false; }
}
