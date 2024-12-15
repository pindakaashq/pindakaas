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

//  Alternative way of dealing with matrix derefs. Direct decomposition into
//  logic and equality. 

public class TransformMatrixDerefDecomp extends TreeTransformerBottomUpNoWrapper
{
    public TransformMatrixDerefDecomp(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    // Decompose (Safe) Element.  idx!=i \/ result=V[i]  for all i. 
        if(curnode instanceof ToVariable && (curnode.getChild(0) instanceof SafeMatrixDeref || curnode.getChild(0) instanceof MatrixDeref)) {
            return decomp(curnode.getChild(0).getChildren(1), curnode.getChild(1), curnode.getChild(0).getChildConst(0));
        }
        
        // Case where matrix deref is not inside a ToVariable. It must be of type
        // boolean and contained in a logic expression or Top
        if( (curnode instanceof SafeMatrixDeref || curnode instanceof MatrixDeref) && !(curnode.getParent() instanceof ToVariable) ) {
            return decomp(curnode.getChildren(1), new BooleanConstant(true), curnode.getChildConst(0));
        }
        
        return null;
    }
    
    private NodeReplacement decomp(ArrayList<ASTNode> idx, ASTNode result, ASTNode mat) {
        
        ArrayList<ASTNode> conjunction=new ArrayList<>();
        ArrayList<ASTNode> ct=new ArrayList<>();
        
        for(int i=0; i<idx.size()+1; i++) {
            ct.add(null);
        }
        
        summat(idx, 0, result, mat, conjunction, ct);
        
        return new NodeReplacement(new And(conjunction));
    }
    
    private void summat(ArrayList<ASTNode> idx, int idxpos, ASTNode result, ASTNode mat, ArrayList<ASTNode> conjunction, ArrayList<ASTNode> ct) {
        if(idxpos==idx.size()) {
            ct.set(idxpos, new Equals(result, mat));
            conjunction.add(new Or(ct));  //  Base case: make the implication constraint.
        }
        else {
            ArrayList<Intpair> idxDomain = idx.get(idxpos).getIntervalSetExp();
            ArrayList<Intpair> matIdxDomain = mat.getIndexDomains().get(0).getIntervalSet();
            idxDomain = Intpair.intersection(idxDomain, matIdxDomain);
            
            for(Intpair idxpair : idxDomain) {
                for(long i=idxpair.lower; i<=idxpair.upper; i++) {
                    ct.set(idxpos, new AllDifferent(idx.get(idxpos), NumberConstant.make(i)));
                    summat(idx, idxpos+1, result, index(mat, matIdxDomain, i), conjunction, ct);
                }
            }
        }
    }
    
    private ASTNode index(ASTNode mat, ArrayList<Intpair> matIdxDomain, long i) {
        int childidx=(int) Intpair.location(matIdxDomain, i);
        return mat.getChildConst(childidx+1);
    }
}

