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

// !(A /\ B)    <----   (!A  \/  !B)
// !(A \/ B)    <----   (!A /\  !B)
// One of the 'branching' transformations. 

public class TransformReverseDeMorgans extends TreeTransformerBottomUpNoWrapper
{
    public TransformReverseDeMorgans(boolean _NegateAnd) {
        super(null);
        NegateAnd=_NegateAnd;
    }
    
    private boolean NegateAnd;   //  First case in comment above.  
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    if( (NegateAnd && curnode instanceof Or) ||  (!NegateAnd && curnode instanceof And) ) {
            
	        // Collect negated children
	        ArrayList<Integer> neg=new ArrayList<Integer>();
	        for(int i=0; i<curnode.numChildren(); i++) {
	            if(curnode.getChild(i) instanceof Negate) {
	                neg.add(i);
	            }
	        }
	        
	        if(neg.size()>1) {
	            // Do the inverse De Morgan's. 
	            ArrayList<ASTNode> outer=curnode.getChildren();
	            ArrayList<ASTNode> inner=new ArrayList<ASTNode>();
	            
	            for(int i=neg.size()-1; i>=0; i--) {
	                inner.add(new Negate(outer.get(i)));   // The two negates will cancel out. 
	                outer.remove(i);
	            }
	            
	            if(NegateAnd) {
	                ASTNode innerct=new Negate(new And(inner));
	                outer.add(innerct);
	                return new NodeReplacement(new Or(outer));
	            }
	            else {
	                ASTNode innerct=new Negate(new Or(inner));
	                outer.add(innerct);
	                return new NodeReplacement(new And(outer));
	            }
	        }
	    }
	    return null;
	}
}

