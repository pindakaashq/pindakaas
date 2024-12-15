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




import savilerow.expression.*;
import savilerow.model.Model;


public abstract class TreeTransformerBottomUpMS extends TreeTransformerBottomUp
{
    /**
	 * Traverse the tree rooted at e, and apply processNode to every node.
	 * Processes children before the parent.
	 * 
	 */
	
	//  When the tree is changed above, the current node becomes detached. So 
	//  the backtracking is simple, just backtrack if the current node is 
	//  detached. 
	
	TreeTransformerBottomUpMS(Model _m) {
	    super(_m);
	}
	
  /* ===========================================================================
    Conjoins an extra constraint expression to the containing relational context
    Must be called after replaceCurrentNode, if both are used.
  =========================================================================== */
    
    protected void addToRelationalContext(ASTNode curnode, ASTNode cons)
    {
        if(cons==null) return;
        
        // Go up the tree from curnode til we find a relation or a catchUndef function.
        while(curnode != null && !(curnode.isRelation() && curnode.getDimension()==0) && !(curnode instanceof CatchUndef))
        {
            assert !curnode.isDetached();
            curnode=curnode.getParent();
        }
        
        if(curnode==null) {
            // We must not be in m.constraints
            // Add to main conjunction in the model.
            relContextConstraint=new And(relContextConstraint, cons);
        }
        else {
            if(curnode instanceof CatchUndef) {
                // Call a special method on catchUndef to make the expression replacing the catchUndef.
                ASTNode repl=((CatchUndef)curnode).replacementExp(cons);
                curnode.getParent().setChild(curnode.getChildNo(), repl);
            }
            else {
                // replace
                curnode.getParent().setChild(curnode.getChildNo(), new And(cons, curnode));
            }
            assert curnode.isDetached();
        }
    }
}
