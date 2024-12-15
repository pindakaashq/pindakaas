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

public class BooleanDomain extends SimpleDomain
{
    public static final long serialVersionUID = 1L;
    public BooleanDomain(ASTNode a) {
        // a could be a value or  a Range
        super(a);
    }
    
    // This simplify could slow things down.
    public ASTNode simplify() {
        if(getChild(0) instanceof Range && getChild(0).getChild(0).isConstant() && getChild(0).getChild(1).isConstant()) {
            if(getChild(0).getChild(0).getValue()==0 && getChild(0).getChild(1).getValue()==1) {
                return new BooleanDomainFull();
            }
        }
        return null;
    }
    
    public ASTNode copy() {
	    return new BooleanDomain(getChild(0));
	}
	public Intpair getBounds() {
	    return getChild(0).getBounds();
	}
	
	public ArrayList<Intpair> getIntervalSet() {
	    return getChild(0).getIntervalSet();
	}
	
	public boolean containsValue(long val) {
	    return getChild(0).containsValue(val);
	}
	
	@Override
	public boolean isBooleanSet() {
	    return true;
	}
	
	@Override
    public boolean isFiniteSet() {
        return true;
    }
    @Override
    public boolean isFiniteSetUpper() {
        return true;
    }
    @Override
    public boolean isFiniteSetLower() {
        return true;
    }
    @Override
    public boolean isConstantSet() {
        if(getChild(0) instanceof Range && getChild(0).getChild(0).isConstant() && getChild(0).getChild(1).isConstant()) {
            return true;
        }
        if(getChild(0).isConstant()) {
            return true;
        }
        return false;
    }
    
	public String toString() {
	    String st="bool";
        if(!containsValue(0) && !containsValue(1)) {
            st+="(true..false)";   // Empty domain.
        }
        else if(!containsValue(0)) {
            st+="(true)";
        }
        else if(!containsValue(1)) {
            st+="(false)";
        }
	    return st;
	}
}
