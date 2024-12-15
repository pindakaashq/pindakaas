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

// Turn product into MultiplyMapper for SAT

//  If more than two children, it collects const/param/quantifier in one product and
//  decision expressions in another product, applying the MultiplyMapper to the
//  two products. 

public class TransformProductToMult extends TreeTransformerBottomUpNoWrapper
{
    public TransformProductToMult(Model mod) {
        super(mod);
    }
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof Times) {
	        //  Collect constants/parameters into one list, decision expressions into another.
	        ArrayList<ASTNode> consts=new ArrayList<ASTNode>();
	        ArrayList<ASTNode> vars=new ArrayList<ASTNode>();
	        for(int i=0; i<curnode.numChildren(); i++) {
	            if(curnode.getChild(i).getCategory() <= ASTNode.Quantifier) {
	                consts.add(curnode.getChild(i));
	            }
	            else {
	                vars.add(curnode.getChild(i));
	            }
	        }
	        
	        if(consts.size()>0 && vars.size()>0) {
	            return new NodeReplacement(new MultiplyMapper(new Times(vars), new Times(consts)));
	        }
	    }
	    return null;
	}
}
