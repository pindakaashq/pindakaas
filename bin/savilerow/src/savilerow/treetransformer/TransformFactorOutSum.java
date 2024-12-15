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
import java.util.HashMap;

import savilerow.expression.*;

// (a+b)c  ->  ac+bc
// One of the 'branching' transformations.
// Opposite of MultiplyOutSum

public class TransformFactorOutSum extends TreeTransformerBottomUpNoWrapper
{
    public TransformFactorOutSum() {
        super(null);
    }
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof WeightedSum) {
	        HashMap<ASTNode, ArrayList<Integer>> terms=new HashMap<ASTNode, ArrayList<Integer>>();
	        
	        // Populate terms
	        for(int i=0; i<curnode.numChildren(); i++) {
	            if(curnode.getChild(i) instanceof Times) {
	                ASTNode t=curnode.getChild(i);
	                
	                // For every unique term in t, add to the hashmap. 
	                
	                ArrayList<ASTNode> uniq=t.getChildren();
	                for(int j=0; j<uniq.size(); j++) {
	                    for(int k=j+1; k<uniq.size(); k++) {
	                        if(uniq.get(j).equals(uniq.get(k))) {
	                            uniq.remove(k);
	                            k--;
	                        }
	                    }
	                }
	                
	                for(int j=0; j<uniq.size(); j++) {
	                    ASTNode prodterm=uniq.get(j);
	                    if(terms.containsKey(prodterm)) {
	                        terms.get(prodterm).add(i);
	                    }
	                    else {
	                        ArrayList<Integer> tmp=new ArrayList<Integer>();
	                        tmp.add(i);
	                        terms.put(prodterm, tmp);
	                    }
	                }
	            }
	            else {
	                // Might have 2z and xyz, and need to factor out z.
	                // So need to include ones that are not in a Times. 
	                ASTNode prodterm=curnode.getChild(i);
                    if(terms.containsKey(prodterm)) {
                        terms.get(prodterm).add(i);
                    }
                    else {
                        ArrayList<Integer> tmp=new ArrayList<Integer>();
                        tmp.add(i);
                        terms.put(prodterm, tmp);
                    }
	            }
	        }
	        
	        // Unfortunately taking out one factor may prevent others. 
	        // Heuristic: Take factor out of greatest number of terms first. 
	        
	        // Can get away with just taking one factor out. If another one
	        // happens to be in the exact same set of terms, this will be taken out
	        // by another pass of this rule. 
	        
	        ASTNode factor=null;
	        int numterms=-1;
	        
	        for(ASTNode prodterm : terms.keySet()) {
	            if(terms.get(prodterm).size()>numterms) {
	                factor=prodterm;
	                numterms=terms.get(prodterm).size();
	            }
	        }
	        
	        if(numterms>1) {
	            // Factor it out. 
	            ArrayList<ASTNode> innersumch=new ArrayList<ASTNode>();
	            ArrayList<Long> innersumweights=new ArrayList<Long>();
	            
	            ArrayList<Integer> occurrences=terms.get(factor);
	            
	            for(Integer i : occurrences) {
	                long wt=((WeightedSum)curnode).getWeight(i);
	                innersumweights.add(wt);
	                
	                if(curnode.getChild(i) instanceof Times) {
	                    ArrayList<ASTNode> timeschild=curnode.getChild(i).getChildren();
	                    timeschild.remove(factor);
	                    
	                    innersumch.add(new Times(timeschild));
	                }
	                else {
	                    assert curnode.getChild(i).equals(factor);
	                    innersumch.add(NumberConstant.make(1));
	                }
	            }
	            
	            ASTNode innersum=new WeightedSum(innersumch, innersumweights);
	            
	            ArrayList<ASTNode> outersumch=curnode.getChildren();
	            ArrayList<Long> outersumweights=((WeightedSum)curnode).getWeights();
	            for(int i=occurrences.size()-1; i>=0; i--) {
	                int j=occurrences.get(i);
	                outersumch.remove(j);
	                outersumweights.remove(j);
	            }
	            
	            outersumch.add(new Times(factor, innersum));
	            outersumweights.add(1L);
	            ASTNode outersum=new WeightedSum(outersumch, outersumweights);
	            //System.out.println(curnode+"    ----->     "+outersum);
	            return new NodeReplacement(outersum);
	        }
	    }
	    return null;
	}
}
