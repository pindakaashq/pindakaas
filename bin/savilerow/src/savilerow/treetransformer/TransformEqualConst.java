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

//  Transform equality with a constant/single identifier/matrixderef[constants] into a tovariable, before flattening.
// It's a special-case flattener.
// Works when one side of the equality needs to be flattened, and the other side is atomic, and does the flattening without an aux variable.
// Must avoid applying to a boolean expression on one side with integer variable on the other. 

public class TransformEqualConst extends TreeTransformerBottomUpNoWrapper
{
    public TransformEqualConst(boolean _propagate) {
        super(null);
        propagate=_propagate;
    }
    private boolean propagate;
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof Equals || curnode instanceof Iff) {
	        ASTNode c0=curnode.getChild(0);
	        ASTNode c1=curnode.getChild(1);
	        
	        if( (c0.isConstant() || c0 instanceof Identifier) && c1.toFlatten(propagate) && (!c1.isRelation() || c0.isRelation()) ) {
	            return new NodeReplacement(new ToVariable(c1, c0));
	        }
	        if( (c1.isConstant() || c1 instanceof Identifier) && c0.toFlatten(propagate) && (!c0.isRelation() || c1.isRelation()) ) {
	            return new NodeReplacement(new ToVariable(c0, c1));
	        }
	    }
	    
        return null;
    }
}
