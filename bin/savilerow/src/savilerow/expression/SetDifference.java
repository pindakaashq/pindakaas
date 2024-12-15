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

// Set difference for sets that are constant after parameter substitution.

class SetDifference extends SetBinOp
{
    public static final long serialVersionUID = 1L;
	public SetDifference(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public ASTNode copy()
	{
	    return new SetDifference(getChild(0), getChild(1));
	}
	
	public boolean toFlatten(boolean propagate) { return false;}
	
    public ASTNode simplify() {
        
        if(getChild(0).getCategory()==ASTNode.Constant && getChild(1).getCategory()==ASTNode.Constant) {
            ArrayList<Intpair> diff=Intpair.setDifference(getChild(0).getIntervalSet(), getChild(1).getIntervalSet());
            
            return Intpair.makeDomain(diff, this.isBooleanSet());
        }
        return null;
    }
    public boolean isSet() {
        return true;
    }
    public boolean isFiniteSet() {
        return this.isFiniteSetUpper() && this.isFiniteSetLower();
    }
    public boolean isFiniteSetUpper() {
        return getChild(0).isFiniteSetUpper() || !getChild(1).isFiniteSetUpper();
    }
    public boolean isFiniteSetLower() {
        return getChild(0).isFiniteSetLower() || !getChild(1).isFiniteSetLower();
    }
    public boolean isBooleanSet() {
        // If they are not both boolean, then the bools get cast to integers.
        return getChild(0).isBooleanSet() && getChild(1).isBooleanSet();
    }
    
    // Cannot perform set difference operation in bounds methods because 
    // getChild(1).getBounds() is an overestimate of the true set, thus would subtract too much.
    public Intpair getBounds() {
        return getChild(0).getBounds();
    }
	
    public boolean containsValue(long val) {
	    return getChild(0).containsValue(val) && !(getChild(1).containsValue(val));
	}
	
	public String toString() {
	    return "("+getChild(0)+" - "+getChild(1)+")";
	}
}
