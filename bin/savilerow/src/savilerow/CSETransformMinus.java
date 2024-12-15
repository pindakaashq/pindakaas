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





// Put unary - on expression
import java.util.ArrayList;

import savilerow.expression.*;

public class CSETransformMinus extends CSETransform {
    public boolean applicable(ASTNode a) {
        return true;
    }
    
    public ASTNode transform(ASTNode a) {
        return new UnaryMinus(a);
    }
    long neg(long a) {
        if(a==Long.MIN_VALUE) return Long.MAX_VALUE;
        return -a;
    }
    public ASTNode inverse_transform_domain(ASTNode dom) {
        ArrayList<Intpair> pairs=dom.getIntervalSet();
        ArrayList<Intpair> newpairs=new ArrayList<Intpair>(pairs);
        for(int i=0; i<pairs.size(); i++) {
            Intpair p=pairs.get(i);
            // swap and negate the interval.
            
            long tmp=neg(p.lower);
            p.lower=neg(p.upper);
            p.upper=tmp;
            
            newpairs.set(pairs.size()-i-1, p); // reverse the order in newpairs
        }
        
        return Intpair.makeDomain(newpairs, false);
    }
}

