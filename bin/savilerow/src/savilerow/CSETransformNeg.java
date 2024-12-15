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





// This is a very simple Active CSE transformation. Just negate the expression.
// It will be simplified and normalised by CSEActive.  
import java.util.ArrayList;

import savilerow.expression.*;

// This reformulation includes Andrea's Active Negation and Active De Morgan's

// De Morgans example:

// Suppose we started with:
//  A \/ B \/ C <-> b1
//  !(A \/ B \/ C) <-> b2

// This gets simplified to 
//  A \/ B \/ C <-> b1
//  !A /\ !B /\ !C <-> b2




public class CSETransformNeg extends CSETransform {
    public boolean applicable(ASTNode a) {
        return a.isRelation();  // Can it be negated. 
    }
    
    public ASTNode transform(ASTNode a) {
        return new Negate(a);
    }
    public ASTNode inverse_transform_domain(ASTNode dom) {
        ArrayList<Intpair> pairs=dom.getIntervalSet();
        assert pairs.size()==1;
        
        if(pairs.get(0).lower==1) {
            return new BooleanDomain(NumberConstant.make(0));
        }
        if(pairs.get(0).upper==0) {
            return new BooleanDomain(NumberConstant.make(1));
        }
        return dom;  // same as input.
    }
}

