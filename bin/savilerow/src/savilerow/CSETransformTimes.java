package savilerow;
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

import savilerow.expression.*;

// Divide an expression by a constant.
// Multiply the aux variable by the same constant. 

public class CSETransformTimes extends CSETransform {
    public long num;
    public CSETransformTimes(long _num) {
        num=_num;
    }
    
    public boolean applicable(ASTNode a) {
        return true;
    }
    
    public ASTNode transform(ASTNode id) {
        return new Times(NumberConstant.make(num),id);   // Wrap the aux variable. 
    }
    long product_saturate(long a) {
        long b=a*num;
        if( (b/num)!=a)  {
            // Overflow
            if( (a<0) != (num<0) ) {
                // If either is negative..
                return Long.MIN_VALUE;
            }
            else {
                return Long.MAX_VALUE;
            }
        }
        return b;
    }
    public ASTNode inverse_transform_domain(ASTNode dom) {
        ArrayList<Intpair> pairs=dom.getIntervalSet();
        ArrayList<Intpair> newpairs=new ArrayList<Intpair>(pairs);
        for(int i=0; i<pairs.size(); i++) {
            Intpair p=pairs.get(i);
            
            if(num<0) {
                // swap the interval.
                long tmp=product_saturate(p.lower);
                p.lower=product_saturate(p.upper);
                p.upper=tmp;
            }
            else {
                p.upper=product_saturate(p.upper);
                p.lower=product_saturate(p.lower);
            }
            
            if(num<0) {
                newpairs.set(pairs.size()-i-1, p); // reverse the order in newpairs
            }
            else {
                newpairs.set(i, p);
            }
        }
        
        return Intpair.makeDomain(newpairs, false);
    }
}

