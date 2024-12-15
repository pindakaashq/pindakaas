package savilerow.treetransformer;
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
import savilerow.model.Model;

//  Replace types like SafeDivide with non-safe version and additional variable(s).
//  Applied after unrolling all quantifiers and comprehensions, and before flattening and CSE.

public class TransformRemoveSafeTypes extends TreeTransformerBottomUp
{
    public TransformRemoveSafeTypes(Model m) {
        super(m);
    }
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof SafeDivide || curnode instanceof SafeMod) {
	        boolean div=curnode instanceof SafeDivide;
	        ArrayList<Intpair> denomDomain=curnode.getChild(1).getIntervalSetExp();
	        if(Intpair.in(denomDomain, 0)) {
	            //  Make new auxiliary variable with domain that does not contain 0.
	            ArrayList<Intpair> non0=new ArrayList<Intpair>(2);
	            non0.add(new Intpair(Long.MIN_VALUE, -1));
	            non0.add(new Intpair(1, Long.MAX_VALUE));
	            non0=Intpair.intersection(denomDomain, non0);
	            ASTNode newDenomDomain=Intpair.makeDomain(non0, false);
	            ASTNode aux=m.global_symbols.newAuxiliaryVariable(newDenomDomain);
	            
	            //  Default value of denominator for the undefined case. 
	            ASTNode denomDefault=NumberConstant.make(non0.get(0).lower);
	            
	            ASTNode newcons=new Implies(new AllDifferent(curnode.getChild(1), NumberConstant.make(0)), new Equals(aux, curnode.getChild(1)));
	            newcons=new And(newcons, new Implies(new Equals(curnode.getChild(1), NumberConstant.make(0)), new Equals(aux, denomDefault)));
	            if(curnode instanceof SafeDivide) {
	                return new NodeReplacement(new Divide(curnode.getChild(0), aux), null, newcons);
	            }
	            else {
	                return new NodeReplacement(new Mod(curnode.getChild(0), aux), null, newcons);
	            }
	        }
	        else {
	            //  Just replace with Divide or Mod
	            if(curnode instanceof SafeDivide) {
	                return new NodeReplacement(new Divide(curnode.getChild(0), curnode.getChild(1)));
	            }
	            else {
	                return new NodeReplacement(new Mod(curnode.getChild(0), curnode.getChild(1)));
	            }
	        }
	    }
	    //  Factorial not required -- will be evaluated before output.
	    //  Min and Max not required -- size of input matrix known before 
	    //  flattening, so definedness constraint will be evaluated before min/max
	    //  extracted. 
	    //  SafeElementOne not required -- it simplifies to ElementOne.
	    //  Power/SafePower are turned into a table for any flatzinc/minizinc backend - 
	    //  Gecode and Chuffed have no int_pow constraint and Minizinc has no 
	    //  reified power. 
	    
	    return null;
	}
}
