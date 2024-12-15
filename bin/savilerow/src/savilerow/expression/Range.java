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


import java.util.ArrayList;

import savilerow.CmdFlags;
import savilerow.model.SymbolTable;

// This one can now be an open range or a closed range. 

public class Range extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    
    public Range(ASTNode l, ASTNode r)
    {
        super( (l==null)?new NegInfinity():l,  (r==null)?new PosInfinity():r);
    }
    
    public ASTNode copy()
    {
        return new Range(getChild(0), getChild(1));
    }
    
    @Override
    public boolean equals(Object other)
    {
        if(!(other instanceof Range))
            return false;
        return getChild(0).equals(((ASTNode)other).getChild(0)) && getChild(1).equals(((ASTNode)other).getChild(1));
    }
    
    @Override
    public ASTNode simplify() {
        if(getChild(0).isConstant() && getChild(1).isConstant() && getChild(0).getValue()>getChild(1).getValue()) {
            CmdFlags.warning("interval "+this+" is out of order. Rewriting to empty interval.");
            return new EmptyRange();
        }
        if(getChild(0).equals(getChild(1))) {
            getChild(0).setParent(null);
            return getChild(0);
        }
        return null;
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        for(int i=0; i<2; i++) {
            if (!getChild(i).typecheck(st)) {
                return false;
            }
            if(getChild(i).getDimension() != 0 || !(getChild(i).isNumerical() || getChild(i).isRelation()) ) {
                CmdFlags.println("ERROR: Expected integer type in range: " + this);
                return false;
            }
        }
        return true;
    }
    
    public Intpair getBounds() {
        return new Intpair(getChild(0).getBounds().lower, getChild(1).getBounds().upper);
    }
    
    public String toString() {
        String st="";
        if(! (getChild(0) instanceof NegInfinity)) st+=getChild(0).toString();
        st+="..";
        if(! (getChild(1) instanceof PosInfinity)) st+=getChild(1).toString();
        return st;
    }
    
    public boolean containsValue(long val) {
        return val>=getChild(0).getValue() && val<=getChild(1).getValue();
    }
    
    public boolean toFlatten(boolean propagate) {return false;}
    
    public ArrayList<Intpair> getIntervalSet()
    {
        if(!getChild(0).isConstant() || !getChild(1).isConstant()) {
            return null;
        }
        ArrayList<Intpair> i=new ArrayList<Intpair>(1);
        // Uses Long.MIN_VALUE and Long.MAX_VALUE for unbounded numbers. 
        i.add(new Intpair(getChild(0).getValue(), getChild(1).getValue()));
        return i;
    }
}
