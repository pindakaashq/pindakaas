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


public abstract class TreeTransformerBottomUp extends TreeTransformer
{
    /**
	 * Traverse the tree rooted at e, and apply processNode to every node.
	 * Processes children before the parent.
	 * 
	 */
	
	//  When the tree is changed above, the current node becomes detached. So 
	//  the backtracking is simple, just backtrack if the current node is 
	//  detached. 
	
	Model m;
	TreeTransformerBottomUp(Model _m) {
	    m=_m;
	}
	
    private ArrayList<ASTNode> newConstraints; // Extra constraints created during
    // the transformation, to be ANDed onto the topmost node AFTER the transformation
    // is completed.
    
    public ASTNode relContextConstraint;    //  If a constraint is added to the relational 
    // context, and there is no relational context or Top, then it is stored here.
    
    @Override
    public ASTNode getContextCts() {
        if(relContextConstraint.equals(new BooleanConstant(true))) {
            return null;
        }
        else {
            return relContextConstraint;
        }
    }
    
    public ASTNode transform(ASTNode e)
	{
	    changedTree=false;   // Clear the flag. 
	    assert e!=null;
	    
	    // Deal with case where we are given a part of a tree.
	    
	    ASTNode par=e.getParent();
	    int chno=e.getChildNo();
	    e.setParent(null);
	    
	    // Put e in a box. This covers the case where e itself is replaced -- 
	    // it has a parent so the replacement works as any other. 
	    
	    ASTNode box=new NoTransformBox(e);   // Should not copy e because e's parent pointer is null.
	    // Unless of course e is part of a tree. 
	    
	    // Set up data structures
	    newConstraints=new ArrayList<ASTNode>();
	    relContextConstraint=new BooleanConstant(true);  /// Default value for this
	    
	    recursiveSearch(box);
	    
	    e=box.getChild(0);
	    
	    if(newConstraints.size()==0) {
	        e.setParent(par);  // restore the parent pointer and child number.
	        e.setChildNo(chno); 
	        return e;
	    }
	    else {
	        if(! (e instanceof Top)) {
	            // No Top.  Add to 'relational context' constraints. 
	            relContextConstraint=new And(relContextConstraint, new And(newConstraints));
	        }
	        else {
	            // There is a Top. 
                newConstraints.add(e.getChild(0));
                ASTNode returnval=new And(newConstraints);
                e.setChild(0, returnval);
                e.setParent(par);  // restore the parent pointer and child number.
                e.setChildNo(chno);
	        }
	        return e;
	    }
	}
	
	boolean recursiveSearch(ASTNode curnode) {
        // Return value indicates whether the subtree is completed or not. 
        if(curnode.isDetached()) {
            return false;
        }
        
        // Process all children.
        
        for(int i=0; i<curnode.numChildren(); i++) {
            boolean flag=recursiveSearch(curnode.getChild(i));
            
            // recursive call may have changed something above here. 
            if(curnode.isDetached()) {
                assert !flag;   // sanity check that the tree is not completed
                return false;
            }
            
            if(!flag) i--; // do the same child again.
        }
        
        // Done all the children, now do this node.
        assert !curnode.isDetached();
        
        NodeReplacement r=processNode(curnode);
        if(r!=null) {
            changedTree=true;
            curnode=replaceCurrentNode(curnode, r.current_node);
            addToRelationalContext(curnode, r.rel_context);
            addToConstraints(r.new_constraint);
        }
        
        if(curnode.isDetached()) {
            return false;
        }
        
        return true;
    }
	
  /* ===========================================================================
    Replaces the current node.
  =========================================================================== */
    protected ASTNode replaceCurrentNode(ASTNode curnode, ASTNode replacement)
    {
        if(replacement==null) return curnode;
        
        assert !curnode.isDetached();
        ASTNode parent=curnode.getParent();
        
        int idx=curnode.getChildNo();
        assert parent.getChild(idx)==curnode;
        parent.setChild(idx, replacement);  // leaves the old curnode detached.
        
        assert !parent.getChild(idx).isDetached();
        return parent.getChild(idx);  // Returns the new current node. 
    }
    
  /* ===========================================================================
    Conjoins an extra constraint expression to the containing relational context
    Must be called after replaceCurrentNode, if both are used.
  =========================================================================== */
    
    protected void addToRelationalContext(ASTNode curnode, ASTNode cons)
    {
        if(cons==null) return;
        
        // Go up the tree from curnode til we find a relation
        while(curnode != null && !(curnode.isRelation() && curnode.getDimension()==0))
        {
            //assert curnode.getParent().getChildren().indexOf(curnode)!=-1;
            assert !curnode.isDetached();
            curnode=curnode.getParent();
        }
        
        if(curnode==null) {
            // We must not be in m.constraints
            // Add to main conjunction in the model.
            relContextConstraint=new And(relContextConstraint, cons);
        }
        else {
            // replace
            curnode.getParent().setChild(curnode.getChildNo(), new And(cons, curnode));
            
            assert curnode.isDetached();
            //CmdFlags.println("Added cons to relational context:"+curnode.getParent());
        }
    }
    
  /* ===========================================================================
    Conjoins an extra constraint expression to the top level.
  =========================================================================== */
    
    protected void addToConstraints(ASTNode cons)
    {
        if(cons==null) return;
        newConstraints.add(cons);
    }
}
