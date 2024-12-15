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

// (a+b)c  <-  ac+bc
// One of the 'branching' transformations.
// Opposite of TransformDistributeLogical

public class TransformFactorLogical extends TreeTransformerBottomUpNoWrapper
{
    public TransformFactorLogical(boolean _OrAnd) {
        super(null);
        OrAnd=_OrAnd;
    }
    
    private boolean OrAnd;   //  The expression to factor is an Or of Ands. 
    // Otherwise it's an And of Ors.
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    if( ( OrAnd && curnode instanceof Or) || (!OrAnd && curnode instanceof And) ) {
	        
	        HashMap<ASTNode, ArrayList<Integer>> terms=new HashMap<ASTNode, ArrayList<Integer>>();
	        
	        // Populate terms
	        for(int i=0; i<curnode.numChildren(); i++) {
	            if( (OrAnd && curnode.getChild(i) instanceof And) ||
	                (!OrAnd && curnode.getChild(i) instanceof Or) ) {
	                ASTNode t=curnode.getChild(i);
	                
	                // For every unique term in t, add to the hashmap. 
	                // Should be no need to throw away duplicates, but leaving it in for now just in case. 
	                
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
	                    ASTNode term=uniq.get(j);
	                    if(terms.containsKey(term)) {
	                        terms.get(term).add(i);
	                    }
	                    else {
	                        ArrayList<Integer> tmp=new ArrayList<Integer>();
	                        tmp.add(i);
	                        terms.put(term, tmp);
	                    }
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
	        
	        for(ASTNode term : terms.keySet()) {
	            if(terms.get(term).size()>numterms) {
	                factor=term;
	                numterms=terms.get(term).size();
	            }
	        }
	        
	        if(numterms>1) {
	            // Factor it out. 
	            ArrayList<ASTNode> innerch=new ArrayList<ASTNode>();
	            
	            ArrayList<Integer> occurrences=terms.get(factor);
	            
	            for(Integer i : occurrences) {
	                assert (OrAnd && curnode.getChild(i) instanceof And) || (!OrAnd && curnode.getChild(i) instanceof Or);
	                
                    ArrayList<ASTNode> newchild=curnode.getChild(i).getChildren();
                    newchild.remove(factor);
                    
                    if(OrAnd) {
                        innerch.add(new And(newchild));
                    }
                    else {
                        innerch.add(new Or(newchild));
                    }
	            }
	            
	            ASTNode innerexpression;
	            if(OrAnd) {
	                innerexpression=new Or(innerch);
	            }
	            else {
	                innerexpression=new And(innerch);
	            }
	            
	            ArrayList<ASTNode> outerch=curnode.getChildren();
	            
	            for(int i=occurrences.size()-1; i>=0; i--) {
	                int j=occurrences.get(i);
	                outerch.remove(j);
	            }
	            
	            ASTNode outer;
	            if(OrAnd) {
	                outerch.add(new And(factor, innerexpression));
	                outer=new Or(outerch);
	            }
	            else {
	                outerch.add(new Or(factor, innerexpression));
	                outer=new And(outerch);
	            }
	            
	            //System.out.println(curnode+"    ----->     "+outer);
	            return new NodeReplacement(outer);
	        }
	    }
	    return null;
	}
}
