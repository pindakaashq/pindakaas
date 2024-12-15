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



import java.math.BigInteger;

public class QuantifiedSum extends Quantifier
{
    public static final long serialVersionUID = 1L;
    public QuantifiedSum(ASTNode i, ASTNode d, ASTNode e) {
        super(i,d,e);
    }
    public boolean isNumerical() {
        return true;
    }
    
	public ASTNode copy()
	{
	    return new QuantifiedSum(getChild(0), getChild(1), getChild(2));
	}
	
	public boolean toFlatten(boolean propagate) {
	    return true;
	}
	
	public Intpair getBounds() {
	    Intpair a=getChild(2).getBounds();  // bounds of the contained expression
	    
	    if(getChild(1) instanceof SimpleDomain) {
	        Intpair dombnds=getChild(1).getBounds();
	        BigInteger domsize=BigInteger.valueOf(dombnds.upper).subtract(BigInteger.valueOf(dombnds.lower)).add(BigInteger.valueOf(1));
	        BigInteger low=BigInteger.valueOf(a.lower).multiply(domsize);
            BigInteger up=BigInteger.valueOf(a.upper).multiply(domsize);
            return new Intpair(Intpair.BigIntegerToLong(low), Intpair.BigIntegerToLong(up));
	    }
	    else {
	        assert getChild(1) instanceof MatrixDomain;
	        
	        Intpair dombnds=getChild(1).getChild(0).getBounds();   // Bounds of base domain.
	        BigInteger domsize=BigInteger.valueOf(dombnds.upper).subtract(BigInteger.valueOf(dombnds.lower)).add(BigInteger.valueOf(1));
	        
	        if(domsize.compareTo(BigInteger.valueOf(1))==0) {
	            // No matter how many matrix slots there are, there is only one concrete matrix.
	            return a;
	        }
	        
	        // domsize is now size of base domain. 
	        BigInteger numslots=BigInteger.valueOf(1);  // upper bound on number of items in each matrix.
	        for(int i=3; i<getChild(1).numChildren(); i++) {
	            Intpair idxdombnds=getChild(1).getChild(i).getBounds();
	            BigInteger idxdomsize=BigInteger.valueOf(idxdombnds.upper).subtract(BigInteger.valueOf(idxdombnds.lower)).add(BigInteger.valueOf(1));
	            numslots=numslots.multiply(idxdomsize);
	        }
	        
	        if(numslots.compareTo(BigInteger.valueOf(63)) > 0) {
	            // nummat will be >= 2^63, bail out 
	            return new Intpair(Long.MIN_VALUE, Long.MAX_VALUE);
	        }
	        
	        BigInteger nummat=domsize.pow(numslots.intValue());  // This could be far too big.
	        
	        a.lower=Intpair.BigIntegerToLong(BigInteger.valueOf(a.lower).multiply(nummat));
            a.upper=Intpair.BigIntegerToLong(BigInteger.valueOf(a.upper).multiply(nummat));
            
            return a;
	    }
	}
	
	public ASTNode simplify() {
	    if(! getChild(2).contains(getChild(0)) 
	        && getChild(1).getCategory()==ASTNode.Constant
	        && getChild(1) instanceof SimpleDomain ) {
	        // Identifier not used anywhere.
	        
	        // Multiply by size of the domain.
	        long i=Intpair.numValues(getChild(1).getIntervalSet());
	        getChild(2).setParent(null);
	        return new Times(getChild(2), NumberConstant.make(i));
	    }
	    return null;
	}
	
	public String toString() {
	    return "(sum "+getChild(0)+" : "+getChild(1)+" . "+getChild(2)+")";
	}
}
