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

//  Rewrite ToVar(Element, Var) into logic and equality.

public class TransformElementForSAT3 extends TreeTransformerBottomUpNoWrapper
{
    public TransformElementForSAT3(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    // Decompose (Safe) Element.  idx!=i \/ result=V[i]  for all i. 
	    
        if(curnode instanceof ToVariable && (curnode.getChild(0) instanceof SafeElementOne || curnode.getChild(0) instanceof ElementOne)) {
            ASTNode idx=curnode.getChild(0).getChild(1);
            ASTNode result=curnode.getChild(1);
            ASTNode mat=curnode.getChild(0).getChild(0);
            return decompElement(idx, result, mat);
        }
        
        // Case where element is not inside a ToVariable. It must be of type
        // boolean and contained in a logic expression or Top
        
        if( (curnode instanceof SafeElementOne || curnode instanceof ElementOne) && !(curnode.getParent() instanceof ToVariable) ) {
            return decompElement(curnode.getChild(1), new BooleanConstant(true), curnode.getChild(0));
        }
        
        return null;
    }
    
    private NodeReplacement decompElement(ASTNode idx, ASTNode result, ASTNode mat) {
        // Specialised support encoding. For each variable and value, list its supports. 
        ArrayList<Intpair> domIndex = idx.getIntervalSetExp();
        ArrayList<Intpair> resultIndex = result.getIntervalSetExp();
        
        ArrayList<ASTNode> and=new ArrayList<ASTNode>();
        
        //  support clauses for values of index variable. 
        
        for (Intpair indexPair : domIndex) {
            for (long i = indexPair.lower; i <= indexPair.upper; i++) {
                ArrayList<ASTNode> disj=new ArrayList<ASTNode>();
                
                disj.add(new AllDifferent(idx, NumberConstant.make(i)));
                
                //.. or there is a pair to support value i. 
                
                if(i>=1 && i<mat.numChildren()) {
                    for(Intpair resPair : resultIndex) {
                        for(long j = resPair.lower; j<=resPair.upper; j++) {
                            ASTNode term1 = new Equals(mat.getChild((int) i), NumberConstant.make(j));
                            
                            ASTNode term2 = new Equals(result, NumberConstant.make(j));
                            
                            disj.add(new And(term1, term2));
                        }
                    }
                }
                else {
                    disj.add(new Equals(result, NumberConstant.make(0)));
                }
                
                and.add(new Or(disj));
            }
        }
        
        //  Support clauses for values of the result variable. 
        for(Intpair resPair : resultIndex) {
            for(long j = resPair.lower; j<=resPair.upper; j++) {
                ArrayList<ASTNode> disj=new ArrayList<ASTNode>();
                
                disj.add(new AllDifferent(result, NumberConstant.make(j)));
                
                for (Intpair indexPair : domIndex) {
                    for (long i = indexPair.lower; i <= indexPair.upper; i++) {
                        if(i>=1 && i<mat.numChildren()) {
                            ASTNode term1 = new Equals(mat.getChild((int) i), NumberConstant.make(j));
                            
                            ASTNode term2 = new Equals(idx, NumberConstant.make(i));
                            
                            disj.add(new And(term1, term2));
                        }
                    }
                }
                
                if(j==0) {
                    // If the value of the result variable is 0, then it is supported by all out-of-bounds index values. 
                    for (Intpair indexPair : domIndex) {
                        for (long i = indexPair.lower; i <= indexPair.upper; i++) {
                            if(i<1 || i>=mat.numChildren()) {
                                disj.add(new Equals(idx, NumberConstant.make(i)));
                            }
                        }
                    }
                }
                
                and.add(new Or(disj));
            }
        }
        
        //  For each entry in the matrix, a short (ternary) support clause
        
        for(int i=1; i<mat.numChildren(); i++) {
            ArrayList<Intpair> mdom = mat.getChild(i).getIntervalSetExp();
            for(Intpair mvals : mdom) {
                for(long j=mvals.lower; j<=mvals.upper; j++) {
                    ASTNode term1 = new AllDifferent(mat.getChild(i), NumberConstant.make(j));
                    
                    ASTNode term2 = new AllDifferent(idx, NumberConstant.make(i));
                    
                    ASTNode term3 = new Equals(result, NumberConstant.make(j));
                    
                    and.add(new Or(term1, term2, term3));
                }
            }
        }
        
        return new NodeReplacement(new And(and));
    }
    
}

