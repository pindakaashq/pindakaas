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

// Cast 1-d matrix (non-decision) into a set. 
import java.util.ArrayList;
import java.util.Collections;

import savilerow.model.SymbolTable;

public class ToSet extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
	public ToSet(ASTNode m)
	{
		super(m);
	}
	
	public ASTNode copy() {
	    return new ToSet(getChild(0));
	}
	
	public boolean toFlatten(boolean propagate) { return false; }
	public boolean isNumerical() {
        return false;
    }
    public boolean isSet() {
        return true;
    }
    public boolean isFiniteSet() {
        return true;
    }
    public boolean isFiniteSetUpper() {
        return true;
    }
    public boolean isFiniteSetLower() {
        return true;
    }
    public boolean isBooleanSet() {
        return getChild(0).isRelation();
    }
    public boolean typecheck(SymbolTable st) {
        if(! getChild(0).typecheck(st)) return false;
        if(getChild(0).getDimension()!=1) {
            System.out.println("ERROR: Expected one-dimensional matrix inside toSet function: "+this);
            return false;
        }
        if(getChild(0).getCategory()==ASTNode.Decision) {
            System.out.println("ERROR: toSet function contains a decision variable: "+this);
            return false;
        }
        return true;
	}
    public ASTNode simplify() {
        ASTNode mat=getChildConst(0);
        
        if( (mat instanceof EmptyMatrix || mat instanceof CompoundMatrix)
            && mat.getCategory() == ASTNode.Constant) {
            if(mat instanceof EmptyMatrix) {
                return new IntegerDomain(new EmptyRange());
            }
            
            ArrayList<Long> tmp=new ArrayList<Long>();
            for(int i=1; i<mat.numChildren(); i++) {
                tmp.add(mat.getChild(i).getValue());
            }
            
            Collections.sort(tmp);
            
            if(! mat.isRelation()) {
                ArrayList<Intpair> tmp2=new ArrayList<Intpair>();
                
                for(int i=0; i<tmp.size(); i++) {
                    long lower=tmp.get(i);
                    long upper=tmp.get(i);
                    
                    // Scan forward to find the upper bound of an interval.
                    while(i<tmp.size()-1 && tmp.get(i+1)<=upper+1) {
                        upper=tmp.get(i+1);
                        i++;
                    }
                    tmp2.add(new Intpair(lower,upper));
                }
                return new IntegerDomainConcreteArray(tmp2);
            }
            else {
                if(tmp.size()==0) {
                    return new BooleanDomain(new EmptyRange());
                }
                else {
                    return new BooleanDomain(new Range(NumberConstant.make(tmp.get(0)), NumberConstant.make(tmp.get(tmp.size()-1))));
                }
            }
        }
	    return null;
	}
	
	public Intpair getBounds() {
	    return getChild(0).getBounds();
	}
	
	public String toString() {
	    return "toSet("+getChild(0)+")";
	}
}