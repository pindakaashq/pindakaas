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




import java.util.HashMap;
import java.util.Map;

// This class represents an arbitrary function from integers to integers. Used to deal
// with matrices indexed by e.g. int(1,3,5) by having a function 1->0, 3->1, 5->2, so return value of this function is 0,1,2
// Maps any unmapped values to a dummy value max+1, this avoids constraining the child var when this is flattened.

public class Mapping extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public HashMap<Long, Long> map;
    public long defaultval;
    public Mapping(HashMap<Long, Long> _map, ASTNode a)
    {
        super(a);
        map=_map;
        
        // set defaultval.
        Long upper=null;
	    for(Map.Entry<Long, Long> it : map.entrySet()) {
	        long val=it.getValue();
	        if(upper == null || upper<val) upper=val;
	    }
	    defaultval=upper+1;
    }
    
    public Mapping(HashMap<Long, Long> _map, long defval, ASTNode a) {
        super(a);
        map=_map;
        defaultval=defval;
    }
    
    public String toString()
    {
        return "Mapping("+map.toString()+", "+getChild(0)+")";
    }
    
	public ASTNode copy()
	{
	    return new Mapping(map, defaultval, getChild(0));
	}
	@Override
	public boolean equals(Object other)
	{
	    if(! (other instanceof Mapping))
	        return false;
	    return ((Mapping)other).map.equals(map) && getChild(0).equals(((Mapping)other).getChild(0)) && ((Mapping)other).defaultval==defaultval;
	}
	
	@Override
    public int hashCode() {
        if(hashCache==Integer.MIN_VALUE) {
            int hash = 5573*getChild(0).hashCode() + 4003*map.hashCode() + 1433*((int)defaultval);
            hashCache=hash;  // store
            return hash;
        }
        else {
            return hashCache;
        }
    }
	
	public boolean toFlatten(boolean propagate) { return true; }
	public boolean isNumerical() {
        return true;
    }
    public boolean strongProp() {
        return getChild(0).strongProp();
    }
    
    public ASTNode simplify() {
	    if(getChild(0).isConstant()) {
	        if(map.containsKey(getChild(0).getValue())) {
	            return NumberConstant.make(map.get(getChild(0).getValue()));
	        }
	        else {
	            return NumberConstant.make(defaultval);
	        }
	    }
	    
	    if(getChild(0) instanceof Mapping) {
	        // Merge the two.
	        HashMap<Long,Long> innermap=((Mapping)getChild(0)).map;
	        long innerdefaultval=((Mapping)getChild(0)).defaultval;
	        
	        HashMap<Long, Long> newmap=new HashMap<Long,Long>();
	        
	        //  For each entry innermap(i) and innerdefaultval, replace with map(innermap(i))
	        for(long i : innermap.keySet()) {
	            long j=innermap.get(i);
	            if(map.containsKey(j)) {
	                newmap.put(i,map.get(j));
	            }
	            //  else defaultval.
	        }
	        
	        if(map.containsKey(innerdefaultval)) {
	            newmap.put(innerdefaultval, map.get(innerdefaultval));
	        }
	        
	        getChild(0).getChild(0).setParent(null);
	        return new Mapping(newmap, defaultval, getChild(0).getChild(0));
	    }
	    
	    return null;
	}
	public Intpair getBounds() {
	    Intpair a=getChild(0).getBounds();
	    long lower=defaultval;   ///  Assumes defaultval is always in.
	    long upper=defaultval;
	    
	    for(long i : map.keySet()) {
	        // Collect entries from map that are within range of the child. 
	        if(i<=a.upper && i>=a.lower) {
                long val=map.get(i);
                if(lower>val) lower=val;
                if(upper<val) upper=val;
            }
	    }
	    
	    return new Intpair(lower, upper);
	}
	
	public PairASTNode getBoundsAST() {
	    // Just look at the table for now.
	    Long lower=null;
	    Long upper=null;
	    
	    for(Map.Entry<Long, Long> a : map.entrySet()) {
	        long val=a.getValue();
	        if(lower == null || lower>val) lower=val;
	        if(upper == null || upper<val) upper=val;
	    }
	    if(lower == null || lower>defaultval) lower=defaultval;
	    if(upper == null || upper<defaultval) upper=defaultval;
	    
	    return new PairASTNode(NumberConstant.make(lower), NumberConstant.make(upper));  // add the default value.
	}
}
