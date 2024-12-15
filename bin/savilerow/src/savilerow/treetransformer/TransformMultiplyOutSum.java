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

// (a+b)c  ->  ac+bc
//  Distribute multiplication over sum. 
// One of the 'branching' transformations. 

public class TransformMultiplyOutSum extends TreeTransformerBottomUpNoWrapper
{
    public TransformMultiplyOutSum() {
        super(null);
    }
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof Times) {
	        int sumterm=-1;
	        
	        for(int i=0; i<curnode.numChildren(); i++) {
	            if(curnode.getChild(i) instanceof WeightedSum) {
	                sumterm=i;
	                break;
	            }
	        }
	        
	        if(sumterm==-1) return null;   // No sum.
	        
	        ASTNode sum=curnode.getChild(sumterm);
	        
	        ArrayList<ASTNode> rest_ch=curnode.getChildren();
	        rest_ch.remove(sumterm);
	        ASTNode rest=new Times(rest_ch);
	        
	        ArrayList<Long> w=((WeightedSum)sum).getWeights();
	        ArrayList<ASTNode> newsum_ch=new ArrayList<ASTNode>();
	        
	        for(int i=0; i<sum.numChildren(); i++) {
	            newsum_ch.add(new Times(rest, sum.getChild(i)));
	        }
	        
	        return new NodeReplacement(new WeightedSum(newsum_ch, w));  // reuse the weights.
	    }
	    return null;
	}
}
