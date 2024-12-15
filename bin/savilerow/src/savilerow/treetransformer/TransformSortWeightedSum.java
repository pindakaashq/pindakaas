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

//  Sort sums by coefficient to reduce sizes of intermediate variables when the sums are broken up from the left.

//  Should really sort by size of intermediate variables (to be created), but for now just
//  sorting by abs value of coefficient.

public class TransformSortWeightedSum extends TreeTransformerBottomUpNoWrapper
{
    public TransformSortWeightedSum() { super(null); }
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode.getParent() != null && !(curnode.getParent() instanceof Tag)
	        && curnode instanceof WeightedSum) {
            WeightedSum sum=(WeightedSum) curnode;
            ArrayList<Long> weights=sum.getWeights();
            ArrayList<ASTNode> children=sum.getChildren();
            
            // Variant of insertion sort. First pass with j==1 places largest value at right-hand end. 
            // Second pass places second-largest at n-1 position.
            
            boolean swapped=true;
            int j = 0;
            
            while (swapped) {
                swapped = false;
                j++;
                
                for (int i = 0; i < weights.size() - j; i++) {
                    if( Math.abs(weights.get(i)) > Math.abs(weights.get(i+1))) {
                        
                        Long tempWeight=weights.get(i);
                        ASTNode tempChild=children.get(i);
                        
                        weights.set(i, weights.get(i+1));
                        children.set(i, children.get(i+1));
                        
                        weights.set(i+1, tempWeight);
                        children.set(i+1,tempChild);
                        
                        swapped = true;
                    }
                }
            }
            return new NodeReplacement(new Tag(new WeightedSum(children, weights)));
        }
        return null;
    }
}

