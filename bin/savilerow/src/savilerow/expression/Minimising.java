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
import savilerow.model.*;

// One child, a compound matrix or a slice or something.

public class Minimising extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public Minimising(ASTNode r)
    {
        super(r);
    }
    
    public ASTNode copy()
    {
        assert numChildren()==1;
        return new Minimising(getChild(0));
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        if(!getChild(0).typecheck(st)) return false;
        if(getChild(0).getDimension()>1) {
            CmdFlags.println("ERROR: Expected numerical expression or one-dimensional literal matrix in minimising, found a matrix: "+this);
	        return false;
        }
        if(getChild(0).getDimension()==1 && !(getChild(0) instanceof CompoundMatrix)) {
            CmdFlags.println("ERROR: Expected numerical expression or one-dimensional literal matrix in minimising, found a matrix: "+this);
	        return false;
        }
        return true;
    }
    
    public int polarity(int child) {
        return -1;   //  Puts an upper bound on the contained expression.
    }
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("MINIMISING ");
        getChild(0).toMinion(b, false);
        b.append("\n");
    }
    public String toString() {
        return "minimising "+getChild(0)+"\n";
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        if(!getChild(0).isConstant()) {
            b.append("minimize ");
            getChild(0).toFlatzinc(b, false);
            b.append(";\n");
        }
        else {
            b.append("satisfy;\n");
        }
    }
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("minimize ");
        getChild(0).toMinizinc(b, false);
        b.append(";\n");
    }
    public void toSAT(Sat satModel) throws IOException {
        if(getChild(0) instanceof Identifier) {
            ArrayList<Intpair> a=getChild(0).getIntervalSetExp();
            for(int i=0; i<a.size(); i++) {
                Intpair p=a.get(i);
                for(long val=p.lower; val<=p.upper; val++) {
                    //  This should be adaptive -- use whichever variable encoding is
                    //  present. 
                    if(i<a.size()-1 || val<p.upper) {
                        satModel.addSoftClause(getChild(0).orderEncode(satModel, val));
                    }
                    
                    //  direct ver
                    //if(val<a.get(a.size()-1).upper) {
                    //    satModel.addSoftClause(getChild(0).directEncode(satModel, val), a.get(a.size()-1).upper-val);
                    //}
                }
            }
        }
        else {
            assert getChild(0) instanceof MaxSATObjective;
            getChild(0).toSAT(satModel);
        }
    }
    public void toMIP(BufferedWriter b) throws IOException {
        b.append("Minimize\n");
        b.append("obj: ");
        getChild(0).toMIP(b);
        b.append("\n");
    }
}
