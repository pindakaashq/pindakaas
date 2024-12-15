package savilerow.treetransformer;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2017 Peter Nightingale

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

//  To create the Tseitin encoding (or close to it) this class rewrites some
//  expressions close to the leaves of the tree.

public class TransformShiftToIDL extends TreeTransformerBottomUpNoWrapper
{
    public TransformShiftToIDL(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
    {
        if (curnode instanceof Equals || curnode instanceof Less || curnode instanceof LessEqual) {
            if (curnode.getChild(0) instanceof Identifier && curnode.getChild(1) instanceof ShiftMapper) {
                return new NodeReplacement(createReplacement(curnode, curnode.getChild(0), curnode.getChild(1), true));
            }
            else if (curnode.getChild(0) instanceof ShiftMapper && curnode.getChild(1) instanceof Identifier) {
                return new NodeReplacement(createReplacement(curnode, curnode.getChild(1), curnode.getChild(0), false));
            }
        }
        
        return null;
    }
    
    private static ASTNode createReplacement(ASTNode curnode, ASTNode identifier, ASTNode shift, boolean id_first) {
        // Try to transform x = shift(y, n) into x - y = n
        ArrayList<ASTNode> nodes = new ArrayList<>(2);
        nodes.add(identifier);
        nodes.add(shift.getChild(0));
        
        ArrayList<Long> weights = new ArrayList<>(2);
        weights.add(1L);
        weights.add(-1L);
        
        WeightedSum sum = new WeightedSum(nodes, weights);
        
        if(curnode instanceof Equals) {
            return new Equals(sum, shift.getChild(1));
        }
            
        // Check if the identifier was first or second to maintain consistency
        if(id_first) {
            if(curnode instanceof Less) {
                return new Less(sum, shift.getChild(1));
            }
            else {
                return new LessEqual(sum, shift.getChild(1));
            }
        }
        else {
            if(curnode instanceof Less) {
                return new Less(shift.getChild(1), sum);
            }
            else {
                return new LessEqual(shift.getChild(1), sum);
            }
        }
    }
}
