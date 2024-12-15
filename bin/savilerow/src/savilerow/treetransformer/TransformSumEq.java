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
import savilerow.model.Sat;

//  Transform a tovariable(sum, aux) into and(sumleq, sumgeq) ahead of Minion output. 
//  Same for SAT except avoid sums that are candidates for the special AMO encodings (boolean exactly-one)

public class TransformSumEq extends TreeTransformerBottomUpNoWrapper
{
    boolean propagate;
    public TransformSumEq(boolean _propagate) { 
        super(null);
        propagate=_propagate;
    }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof ToVariable && curnode.getChild(0) instanceof WeightedSum)
        {
            if(!propagate && CmdFlags.getSattrans() && Sat.eligibleAMO(curnode.getChild(0))) {
                return null;    //  Encode as an exactly-one with a special-purpose AMO/EO encoding.
            }
            else if(curnode.getChild(0).numChildren()==1 && ((WeightedSum)curnode.getChild(0)).getWeight(0)==-1) {
                // Special case, need to output a minuseq. Leave the sum intact. 
                return null;
            }
            else {
                return new NodeReplacement(new And(
                    new LessEqual(curnode.getChild(0), curnode.getChild(1)), 
                    new LessEqual(curnode.getChild(1), curnode.getChild(0))
                    ));
            }
        }
        return null;
    }
}

