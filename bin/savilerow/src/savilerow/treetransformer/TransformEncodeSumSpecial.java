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

//  Special cases of encoding sum to SAT. Boolean sum >0, >=1 (to a clause),
//  <2, <=1  (to a ladder encoding)

public class TransformEncodeSumSpecial extends TreeTransformerBottomUp
{
    public TransformEncodeSumSpecial(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof Less || curnode instanceof LessEqual) {
	        if(curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant() && checkAllBool(curnode.getChild(0)) ) {
	            long val=curnode.getChild(1).getValue();
	            if( (curnode instanceof Less && val==2) || (curnode instanceof LessEqual && val==1) ) {
	                // sum<=1
	                // Ladder encoding. Don't forget to check we are top-level.
	                
	                if(curnode.getParent().inTopAnd()) {
	                    System.out.println("USING THE NEW LADDER BIT.");
	                    ArrayList<ASTNode> contents=curnode.getChild(0).getChildren();
	                    
	                    //  Bools indicating if there is a one/true to the left. 
	                    ArrayList<ASTNode> oneLeft=new ArrayList<ASTNode>();
	                    
	                    oneLeft.add(contents.get(0)); 
	                    
	                    ArrayList<ASTNode> newcts=new ArrayList<ASTNode>();
	                    
	                    for(int i=1; i<contents.size(); i++) {
	                        ASTNode newaux=m.global_symbols.newAuxiliaryVariable(0,1);
	                        
	                        // Ladder constraint. 
	                        newcts.add(new Implies(oneLeft.get(oneLeft.size()-1), newaux));
	                        
	                        // If item in contents array is true, the current oneLeft must be true and the previous one must be false. 
	                        
	                        newcts.add(new Implies(contents.get(i), newaux));
	                        newcts.add(new Implies(contents.get(i), new Negate(oneLeft.get(oneLeft.size()-1))));
	                        
	                        // If we have the false then true pattern in the ladder, then the contents array has to contain true.
	                        newcts.add(new Or(oneLeft.get(oneLeft.size()-1), new Negate(newaux), contents.get(i)));
	                        
	                        oneLeft.add(newaux);
	                    }
	                    
	                    return new NodeReplacement(new And(newcts));
	                }
	            }
	            
	            // This case should be a general sum optimisation. Force all members of the sum to their minimum value. 
	            if( (curnode instanceof Less && val==1) || (curnode instanceof LessEqual && val==0) ) {
	                // sum<=0
	                // Assign all to 0.
	                ArrayList<ASTNode> newcts=new ArrayList<ASTNode>();
	                for(int i=0; i<curnode.getChild(0).numChildren(); i++) {
	                    newcts.add(new Equals(curnode.getChild(0).getChild(i), NumberConstant.make(0)));
	                }
	                return new NodeReplacement(new And(newcts));
	            }
	            
	        }
	        else if(curnode.getChild(1) instanceof WeightedSum && curnode.getChild(0).isConstant() && checkAllBool(curnode.getChild(1)) ) {
                long val=curnode.getChild(0).getValue();
                if( (curnode instanceof Less && val==0) || (curnode instanceof LessEqual && val==1) ) {
                    // sum >= 1.   Replace with Or, should encode as a single clause (when top level).
                    return new NodeReplacement(new Or(curnode.getChild(1).getChildren()));
                }
	            
	            // This case should be a general sum optimisation. Force all members of the sum to their maximum value. 
	            if( (curnode instanceof Less && val==curnode.getChild(1).numChildren()-1) || (curnode instanceof LessEqual && val==curnode.getChild(1).numChildren()) ) {
	                // sum>= length(sum)
	                // Assign all to 1.
	                ArrayList<ASTNode> newcts=new ArrayList<ASTNode>();
	                for(int i=0; i<curnode.getChild(1).numChildren(); i++) {
	                    newcts.add(new Equals(curnode.getChild(1).getChild(i), NumberConstant.make(1)));
	                }
	                return new NodeReplacement(new And(newcts));
	            }
	        }
	    }
	    
        return null;
    }
    
    private boolean checkAllBool(ASTNode sum) {
        for(int i=0; i<sum.numChildren(); i++) {
            Intpair bnds=sum.getChild(i).getBounds();
            if(bnds.lower<0 || bnds.upper>1) {
                // Not all bools/0-1 in sum. 
                return false;
            }
        }
        return true;
    }
}

