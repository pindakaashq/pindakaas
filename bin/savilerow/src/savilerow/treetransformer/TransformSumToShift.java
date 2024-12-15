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

// Turn sums into shift and multiply mappers whenever possible because they're better for SAT backend

public class TransformSumToShift extends TreeTransformerBottomUpNoWrapper
{
    public TransformSumToShift(Model mod) {
        super(mod);
    }
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof WeightedSum) {
	        WeightedSum cursum=(WeightedSum) curnode;
	        int numdecisionvars=0;
	        int decvarpos=-1;
	        for(int i=0; i<curnode.numChildren() && numdecisionvars<2; i++) {
	            if(curnode.getChild(i).getCategory()>ASTNode.Quantifier) {
	                numdecisionvars++;
	                decvarpos=i;
	            }
	        }
	        
	        if(numdecisionvars==1) {
	            ASTNode decisionvar=curnode.getChild(decvarpos);
	            ASTNode shift=NumberConstant.make(0);
	            ArrayList<Long> weights=cursum.getWeights();
	            
	            for(int i=0; i<curnode.numChildren(); i++) {
	                if(i!=decvarpos) {
	                    shift=BinOp.makeBinOp("+", shift, new Times(NumberConstant.make(weights.get(i)), curnode.getChild(i)));
	                }
	            }
	            
	            ASTNode mulmap=new MultiplyMapper(decisionvar, NumberConstant.make(weights.get(decvarpos)));
	            ASTNode shiftmap=new ShiftMapper(mulmap, shift);
	            
	            return new NodeReplacement(shiftmap);
	        }
	    }
	    return null;
	}
}
