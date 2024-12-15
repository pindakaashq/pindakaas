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

// Has children of type range (emptyrange) and parameter expressions
// Children are in order. 

public class IntegerDomain extends SimpleDomain
{
    public static final long serialVersionUID = 1L;
    public IntegerDomain(ArrayList<ASTNode> r)
    {
        if(r.size()==0) {
            r.add(new EmptyRange());
        }
        this.setChildren(r);
    }
    public IntegerDomain(ASTNode[] r)
    {
        if(r.length==0) {
            r=new ASTNode[1];
            r[0]=new EmptyRange();
        }
        this.setChildren(r);
    }
    
    public IntegerDomain(ASTNode a) {
        super(a);
    }
    
    public ASTNode copy() {
	    return new IntegerDomain(getChildren());
	}
	
    public Intpair getBounds() {
        Intpair a=getChild(0).getBounds();
        a.upper=getChild(numChildren()-1).getBounds().upper;
        return a;
    }
	
	public ArrayList<Intpair> getIntervalSet()
	{
	    ArrayList<Intpair> intervals=new ArrayList<Intpair>(numChildren());
	    for(int i=0; i<numChildren(); i++) {
	        ArrayList<Intpair> p=getChild(i).getIntervalSet();
	        if(p==null) {
	            return null;
	        }
	        intervals.addAll(p);
	    }
	    return intervals;
	}
	
	@Override
	public ASTNode simplify() {
        if(numChildren() == 1 && this.getChild(0).getDimension() > 0) {
            // has a single child that is a matrix
            return new ToSet(this.getChild(0));
        }
	    if(this.getCategory()==ASTNode.Constant) {
	        ArrayList<Intpair> a=this.getIntervalSet();
            
            // Now compare pairs to their neighbours and merge if overlapping.
            for(int i=0; i<a.size()-1; i++) {
                Intpair tmp=a.get(i).merge(a.get(i+1));
                if(tmp!=null) {
                    System.out.println("WARNING: Merging two adjacent ranges in IntegerDomain: should never happen."+this);
                    a.set(i, tmp);
                    a.remove(i+1);
                    i--;
                }
            }
            
            if(a.size()==1 && a.get(0).lower>=Integer.MIN_VALUE && a.get(0).upper<=Integer.MAX_VALUE) {
                return new IntegerDomainConcrete((int) a.get(0).lower, (int) a.get(0).upper);
            }
            if(a.size()>=1 && isFiniteSet()) {
                return new IntegerDomainConcreteArray(a);
            }
        }
        return null;
	}
	
	@Override
	public boolean isFiniteSetUpper() {
	    // Is it bounded above. 
	    ASTNode top=getChild(numChildren()-1);
	    if(top instanceof Range && top.getChild(1) instanceof PosInfinity) {
	        return false;
	    }
	    return true;
	}
	@Override
	public boolean isFiniteSetLower() {
	    // Is it bounded below.
	    ASTNode bottom=getChild(0);
	    if(bottom instanceof Range && bottom.getChild(0) instanceof NegInfinity) {
	        return false;
	    }
	    return true;
	}
	
	@Override
	public boolean isFiniteSet() {
	    return isFiniteSetUpper() && isFiniteSetLower();
	}
	
	public boolean toFlatten(boolean propagate) {return false;}
	
	public String toString() {
	    String st="int(";
	    for(int i=0; i<numChildren(); i++) {
	        st+=getChild(i).toString();
	        if(i<numChildren()-1) st+=",";
	    }
	    return st+")";
	}
	
	public boolean containsValue(long val) {
	    ASTNode vali=NumberConstant.make(val);
	    for(int i=0; i<numChildren(); i++) {
	        if(getChild(i).equals(vali)) return true;
	        if(getChild(i) instanceof Range && getChild(i).containsValue(val)) return true;
	    }
	    return false;
	}
}
