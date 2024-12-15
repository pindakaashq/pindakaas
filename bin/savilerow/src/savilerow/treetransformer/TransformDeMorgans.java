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

// !(A /\ B)    ---->   (!A  \/  !B)
// !(A \/ B)    ---->   (!A /\  !B)
// One of the 'branching' transformations. 

public class TransformDeMorgans extends TreeTransformerBottomUpNoWrapper
{
    public TransformDeMorgans(boolean _NegateAnd) {
        super(null);
        NegateAnd=_NegateAnd;
    }
    
    private boolean NegateAnd;   //  First case in comment above.  
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    if( curnode instanceof Negate &&
	        ( (NegateAnd && curnode.getChild(0) instanceof And) ||  (!NegateAnd && curnode.getChild(0) instanceof Or) ) ) {
            
	        ASTNode curchild=curnode.getChild(0);
	        
	        ArrayList<ASTNode> newchildren=new ArrayList<ASTNode>();
	        
	        for(int i=0; i<curchild.numChildren(); i++) {
	            newchildren.add(new Negate(curchild.getChild(i)));
	        }
	        
	        if(NegateAnd) {
	            return new NodeReplacement(new Or(newchildren));
	        }
	        else {
	            return new NodeReplacement(new And(newchildren));
	        }
	    }
	    return null;
	}
}

