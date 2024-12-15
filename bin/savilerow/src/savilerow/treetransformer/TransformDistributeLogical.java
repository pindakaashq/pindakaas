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

// P /\ (Q \/ R)  ----->  (P /\ Q)  \/ (P /\ R)   (Distribute And over Or)
// P \/ (Q /\ R)  ----->  (P \/ Q)  /\ (P \/ R)   (Distribute Or over And -- this one blows up on Plotting).
// One of the 'branching' transformations. 

public class TransformDistributeLogical extends TreeTransformerBottomUpNoWrapper
{
    public TransformDistributeLogical(boolean _AndOverOr, boolean _ExTopLevel) {
        super(null);
        AndOverOr=_AndOverOr;
        ExTopLevel=_ExTopLevel;
    }
    
    private boolean AndOverOr;   //  Distribute And over Or.   Otherwise, distribute Or over And.
    private boolean ExTopLevel;   /// Exclude the top level when distributing And over Or. 
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    // excluding top level And. 
	    if(ExTopLevel && curnode instanceof And && curnode.getParent() instanceof Top) {
	        return null;
	    }
	    
	    if( (AndOverOr && curnode instanceof And)  ||  (!AndOverOr && curnode instanceof Or) ) {
	        int innerterm=-1;
	        
	        for(int i=0; i<curnode.numChildren(); i++) {
	            if( (AndOverOr && curnode.getChild(i) instanceof Or) 
	                ||  (!AndOverOr && curnode.getChild(i) instanceof And) ) {
	                innerterm=i;
	                break;
	            }
	        }
	        
	        if(innerterm==-1) return null; 
	        
	        ASTNode inner=curnode.getChild(innerterm);
	        
	        ArrayList<ASTNode> rest_ch=curnode.getChildren();
	        rest_ch.remove(innerterm);
	        
	        ASTNode rest;
	        if(AndOverOr) {
	            rest=new And(rest_ch);
	        }
	        else {
	            rest=new Or(rest_ch);
	        }
	        
	        ArrayList<ASTNode> newouter_ch=new ArrayList<ASTNode>();
	        
	        for(int i=0; i<inner.numChildren(); i++) {
	            if(AndOverOr) {
	                newouter_ch.add(new And(rest, inner.getChild(i)));
	            }
	            else {
	                newouter_ch.add(new Or(rest, inner.getChild(i)));
	            }
	        }
	        
	        if(AndOverOr) {
	            return new NodeReplacement(new Or(newouter_ch));
	        }
	        else {
	            return new NodeReplacement(new And(newouter_ch));
	        }
	    }
	    return null;
	}
}
