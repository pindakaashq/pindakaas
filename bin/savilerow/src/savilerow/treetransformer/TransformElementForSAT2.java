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

public class TransformElementForSAT2 extends TreeTransformerBottomUpNoWrapper
{
    public TransformElementForSAT2(Model _m) { super(_m); }
    
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
        // Can assume index is a decision variable or mapper, and get its 'domain'. 
        ArrayList<Intpair> domainOfIndex = idx.getIntervalSetExp();
        
        ArrayList<ASTNode> and=new ArrayList<ASTNode>();
        
        for (Intpair indexPair : domainOfIndex) {
            for (long i = indexPair.lower; i <= indexPair.upper; i++) {
                ASTNode auxEquals;
                if (i < 1 || i >= mat.numChildren()) {
                    // If out of bounds.
                    auxEquals = new Equals(result, NumberConstant.make(0));
                }
                else {
                    auxEquals = new Equals(result, mat.getChild((int) i));
                }
                
                and.add(new Implies(new Equals(NumberConstant.make(i), idx), auxEquals));
            }
        }
        return new NodeReplacement(new And(and));
    }
    
}

