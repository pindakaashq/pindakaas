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

//  Get rid of reify(abs()) because Gecode doesn't have it.

public class TransformAbsReify extends TreeTransformerBottomUp
{
    public TransformAbsReify(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof ToVariable && curnode.getChild(0) instanceof ToVariable && curnode.getChild(0).getChild(0) instanceof Absolute)
        {
            // reified abs constraint.
            // Replace with a reified equals, with a new aux var for the absolute value.
            
            // Make new aux var for abs.
            ASTNode auxvar=m.global_symbols.newAuxHelper(curnode.getChild(0).getChild(0));
            
	        ASTNode newmincon=new ToVariable(curnode.getChild(0).getChild(0), auxvar);  // non-reified min constraint
	        
            m.global_symbols.auxVarRepresentsConstraint( auxvar.toString(), curnode.getChild(0).getChild(0).toString());
            return new NodeReplacement(
                new ToVariable(new Equals(auxvar, curnode.getChild(0).getChild(1)), curnode.getChild(1)),
                null,
                newmincon);
        }
        return null;
    }
}

