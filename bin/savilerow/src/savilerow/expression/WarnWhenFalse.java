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

//  Wraps a Boolean expression.  Used by TransformMakeSafe to delay a warning.
//  Warns in two cases:
//  1) If the child evaluates to False
//  2) If it reaches output

public class WarnWhenFalse extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    private String warningWhenFalse;
    private String warningWhenOutput;
    
    public WarnWhenFalse(ASTNode ch, String w1, String w2) {
        super(ch);
        warningWhenFalse=w1;
        warningWhenOutput=w2;
    }
    
    public WarnWhenFalse(ASTNode ch, String w1) {
        super(ch);
        warningWhenFalse=w1;
        warningWhenOutput=null;
    }
    
	public ASTNode copy() {
	    return new WarnWhenFalse(getChild(0), warningWhenFalse, warningWhenOutput);
	}
	
	public ASTNode simplify() {
	    if(getChild(0).isConstant()) {
	        long val=getChild(0).getValue();
	        if(val==0) {
	            CmdFlags.warning(warningWhenFalse);
	        }
	        getChild(0).setParent(null);
	        return getChild(0);
	    }
	    return null;
	}
	
	public boolean isRelation() {
	    return true;
	}
	
	//  Output methods.
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        if(warningWhenOutput!=null) CmdFlags.warning(warningWhenOutput);
        getChild(0).toMinion(b, bool_context);
    }
    public String toString() {
        return getChild(0).toString();
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        if(warningWhenOutput!=null) CmdFlags.warning(warningWhenOutput);
        getChild(0).toFlatzinc(b, bool_context);
    }
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        if(warningWhenOutput!=null) CmdFlags.warning(warningWhenOutput);
        getChild(0).toMinizinc(b, bool_context);
    }
    
    public Long toSATLiteral(Sat satModel) {
        return getChild(0).toSATLiteral(satModel);
	}
    
    public void toSAT(Sat satModel) throws IOException {
        if(warningWhenOutput!=null) CmdFlags.warning(warningWhenOutput);
        getChild(0).toSAT(satModel);
    }

    public void toSMT(SMT satModel) throws IOException {
        if(warningWhenOutput!=null) CmdFlags.warning(warningWhenOutput);
        getChild(0).toSMT(satModel);
    }

    public boolean usesSMTEncoding() {
        return true;
    }

    public void toSATWithAuxVar(Sat satModel, long reifyVar) throws IOException {
        if(warningWhenOutput!=null) CmdFlags.warning(warningWhenOutput);
        getChild(0).toSATWithAuxVar(satModel, reifyVar);
    }
}
