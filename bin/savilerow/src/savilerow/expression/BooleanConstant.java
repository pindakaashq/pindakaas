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

public class BooleanConstant extends ASTNode
{
    public static final long serialVersionUID = 1L;
    boolean b;
    public BooleanConstant(boolean boo)
    {
        b=boo;
    }
    
    public ASTNode copy()
    {
        return new BooleanConstant(b);
    }
    @Override
    public boolean equals(Object other)
    {
        if(!(other instanceof BooleanConstant))
            return false;
        return this.b == ((BooleanConstant)other).b;
    }
    
    @Override
    public int hashCode() {
        if(b) return 643787;
        else return 7812376;
    }
    
    public String toString()
    {
        return ""+b;
    }
    public boolean isRelation(){return true;}
    public boolean isNumerical() {
        return false;
    }
    
    public boolean isConstant() { return true;}
    
    public boolean toFlatten(boolean propagate) { return false;}
    
    public long getValue()
    {
        if(b) return 1;
        else return 0;
    }
    public ArrayList<Intpair> getIntervalSetExp() {
        ArrayList<Intpair> i = new ArrayList<Intpair>();
        long val=b?1:0;
        i.add(new Intpair(val, val));
        return i;
    }
    
    public boolean hasLiteralEncoding() {
        return true;
    }
    // Same methods as Identifier for sat encoding.
    public long directEncode(Sat satModel, long value) {
        if( (b?1:0) == value ) {
            return satModel.getTrue();
        }
        else {
            return -satModel.getTrue();
        }
    }
    public long orderEncode(Sat satModel, long value) {
        if( (b?1:0) <= value) {
            return satModel.getTrue();
        }
        else {
            return -satModel.getTrue();
        }
    }
    
    public void toMinion(BufferedWriter buffer, boolean bool_context) throws IOException {
        ASTNode par=getParent();
        // If it's in a context that expects a constraint...
        if(bool_context) {
            if(b) buffer.append("true()");
            else buffer.append("false()");
        }
        else {
            if(b) buffer.append("1");
            else buffer.append("0");
        }
    }
    public void toSAT(Sat satModel) throws IOException {
        if(!b) {
            satModel.addClause(-satModel.getTrue());  // Should be empty clause
        }
    }
    
    public void toDominionParam(StringBuilder buffer) {
        if(b) buffer.append("1");
        else buffer.append("0");
    }
    public void toFlatzinc(BufferedWriter buffer, boolean bool_context) throws IOException {
        ASTNode par=getParent();
        // If it's in a context that expects a constraint...  What about reify?
        if(par instanceof Top) {
            if(b) buffer.append("constraint bool_eq(true,true);");
            else buffer.append("constraint bool_eq(true,false);");
        }
        else {
            if(!bool_context) {  // in some situations, print as a number
                if(b) buffer.append("1");
                else buffer.append("0");
            }
            else {
                if(b) buffer.append("true");
                else buffer.append("false");
            }
        }
    }
    public void toMinizinc(StringBuilder buffer,  boolean bool_context) {
        if(bool_context) {
            if(b) buffer.append("true");
            else buffer.append("false");
        }
        else {
            if(b) buffer.append("1");
            else buffer.append("0");
        }
    }

    ////////////////////////////////////////////////////////////////////////////
    //  SMT encoding
    @Override
    public boolean usesSMTEncoding() {
        return true;
    }

    public String smtEncodeBool(SMT satModel) {
        if (b)
            return "true";
        else
            return "false";
    }

    public String smtEncodeInt(SMT satModel) {
        if (b)
            return "1";
        else
            return "0";
    }

    public String smtEncodeBV(SMT satModel) {
        if (b)
            return BitVector.toHexString(1);
        else
            return BitVector.toHexString(0);
    }
}