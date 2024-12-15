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

import java.util.HashMap;

import savilerow.expression.*;
import savilerow.model.Model;

//  SafeElementOne -> ElementOne if backend requires it. 

public class TransformSafeElementOne extends TreeTransformerBottomUp
{
    public TransformSafeElementOne(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof SafeElementOne) {
	        Intpair p=curnode.getChild(1).getBounds();
	        ASTNode mat=curnode.getChildConst(0);
	        assert mat instanceof CompoundMatrix;
	        
	        if((p.upper-p.lower+1) < 2*(mat.numChildren()-1) || curnode.getChild(1) instanceof Mapping) {
                // Make a new Mapping which will become a table constraint -- should maintain GAC for most solvers. 
                // Only applied when the range of the index is < 2 times the number of elements in the matrix. 
                
                // TransformTrimElement can leave a WeightedSum here that is a shift e.g. (x+2)
                ASTNode index=curnode.getChild(1);
                long shift=0;
                if(index instanceof WeightedSum && index.numChildren()==2) {
                    if(index.getChild(0).isConstant()) {
                        shift=index.getChild(0).getValue()*((WeightedSum)index).getWeight(0);
                        index=BinOp.makeBinOp("-", index, NumberConstant.make(shift));  // remove the shift from the index expression. 
                    }
                    else if(index.getChild(1).isConstant()) {
                        shift=index.getChild(1).getValue()*((WeightedSum)index).getWeight(1);
                        index=BinOp.makeBinOp("-", index, NumberConstant.make(shift));  // remove the shift from the index expression. 
                    }
                }
                
                HashMap<Long, Long> map=new HashMap<Long, Long>();
                for(long domval=1; domval<=mat.numChildren()-1; domval++) {
                    map.put(domval-shift, domval);
                }
                
                ASTNode mapping=new Mapping(map, 1, index);
                
                // Default value of mapping will be 1 which is in range
                return new NodeReplacement(new ElementOne(curnode.getChild(0), mapping));
            }
            else {
                //  Fallback for large index domains. 
                //  Make a new variable that is within range. 
                ASTNode aux=m.global_symbols.newAuxiliaryVariable(1, mat.numChildren()-1);
                
                //  If within bounds, aux = getChild(1)
                ASTNode c1=new Implies(new And(new LessEqual(NumberConstant.make(1), curnode.getChild(1)), new LessEqual(curnode.getChild(1), NumberConstant.make(mat.numChildren()-1))),
                    new Equals(aux, curnode.getChild(1)));
                
                //  Otherwise, aux=1. 
                ASTNode c2=new Implies(new Or(new Less(curnode.getChild(1), NumberConstant.make(1)), new Less(NumberConstant.make(mat.numChildren()-1), curnode.getChild(1))),
                    new Equals(aux, NumberConstant.make(1)));
                
                return new NodeReplacement(new ElementOne(curnode.getChild(0), aux), null, new And(c1, c2));
            }
        }
        return null;
    }
}
