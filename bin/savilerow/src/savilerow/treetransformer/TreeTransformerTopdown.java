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





import savilerow.expression.ASTNode;
import savilerow.model.Model;


public abstract class TreeTransformerTopdown extends TreeTransformer
{
    /**
	 * Traverse the tree rooted at e, and apply processNode to every node.
	 * Processes parent before the children.
	 * Only allows replacement of the current node at the moment. 
	 */
	
	Model m;
	TreeTransformerTopdown(Model _m) {
	    m=_m;
	}
	
    public ASTNode transform(ASTNode e) {
        changedTree=false;
        return transform_root(e);
    }
    
    public ASTNode transform_root(ASTNode e) {
        // Special case for root node. 
        NodeReplacement r=processNode(e);
        if(r!=null) {
            assert r.rel_context==null && r.new_constraint==null;
            changedTree=true; // It has been replaced at the root. 
            return transform_root(r.current_node);  // Do it again. 
        }
        
        // No change to e.
        return transform_inner(e);
    }
    
	public ASTNode transform_inner(ASTNode e)
	{
	    transform_children(e);
	    for(int i=0; i<e.numChildren(); i++) {
	        transform_inner(e.getChild(i));
	    }
	    return e;
	}
	
	public void transform_children(ASTNode e) {
	    for(int i=0; i<e.numChildren(); i++) {
	        NodeReplacement r=processNode(e.getChild(i));
	        if(r!=null) {
	            assert r.rel_context==null && r.new_constraint==null;
	            changedTree=true;
	            e.setChild(i, r.current_node);
	            i--; // do this one again. 
	        }
	    }
	}
}
