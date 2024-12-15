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

//  A unique one, call the simplify method on curnode -- implements lots of small rules.
//  Must be bottom up so that each node can call methods on its children knowing they
//  are well formed. e.g. not Tag. 

public class TransformSimplify extends TreeTransformerBottomUpNoWrapper
{
    public TransformSimplify() { super(null);}
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    // tree nodes are supposed to be immutable (apart from their child pointers), so if it has changed
	    // then it should be a new node.
	    ASTNode tmp=curnode.simplify();
	    if(tmp!=null) {
	        return new NodeReplacement(tmp);
	    }
	    return null;
    }
}

