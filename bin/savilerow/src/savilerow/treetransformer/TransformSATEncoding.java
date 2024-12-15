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

import savilerow.CmdFlags;
import savilerow.expression.*;
import savilerow.model.Model;

//  To create the Tseitin encoding (or close to it) this class rewrites some
//  expressions close to the leaves of the tree.

public class TransformSATEncoding extends TreeTransformerBottomUpNoWrapper
{
    public TransformSATEncoding(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    // If we are not using SMT or the current node will not have an SMT encoding, we process it
        
	    if (!CmdFlags.getSMTtrans() || !curnode.willSMTEncode()) {
            // Replace expressions that can be represented as a single SAT literal
            // with the literal.
            Long lit=curnode.toSATLiteral(m.satModel);
            if(lit!=null) {
                return new NodeReplacement(new SATLiteral(lit, m));
            }
            
            //  Done Equals, Less, LessEqual, not-equal, negation, Iff
            
            //   Replace numerical comparisons of boolean variables with boolean expressions.
            //   Improves the SAT encoding
            if(curnode instanceof Less && curnode.getChild(0) instanceof SATLiteral && curnode.getChild(1) instanceof SATLiteral) {
                // First one is false, other true.
                return new NodeReplacement(new And(curnode.getChild(0).negation(), curnode.getChild(1)));
            }
            if(curnode instanceof LessEqual && curnode.getChild(0).isRelation() && curnode.getChild(1).isRelation()) {
                // First implies the second.
                return new NodeReplacement(new Or(curnode.getChild(0).negation(), curnode.getChild(1)));
            }
        }

        return null;
    }
}

