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




import savilerow.expression.*;
import savilerow.model.Model;

//  Transform exists quantifiers or comprehensions into decision variables if they are too large to unroll.

public class TransformExistsVar extends TreeTransformerTopdown
{
    public TransformExistsVar(Model _m) {
        super(_m);
    }
    
    long threshold=1000000L;  //  If comprehension is likely to unroll into more than threshold items, then transform it into decision variables.
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    //   An Or function and comprehension.
	    if(curnode.getParent()!=null && curnode.getParent().inTopConjunction() 
	        && curnode instanceof OrVector && curnode.getChild(0) instanceof ComprehensionMatrix) {
	        
	        ASTNode cm=curnode.getChild(0);
	        // Check matrix domains have a fixed size in each dimension.  If not
	        // then we can't replace with a set of decision variables. 
	        for(int i=0; i<cm.getChild(1).numChildren(); i++) {
	            ASTNode cmq=cm.getChild(1).getChild(i);
	            if(cmq.getChild(1) instanceof MatrixDomain) {
	                for(int j=3; j<cmq.getChild(1).numChildren(); j++) {
	                    if(cmq.getChild(1).getChild(j).getCategory()>ASTNode.Constant) {
	                        return null;
	                    }
	                }
	            }
	        }
	        
	        // Get rid of any matrix domains in the comprehension.
	        TransformQuantifiedExpression tqe=new TransformQuantifiedExpression(m);
	        NodeReplacement nr=tqe.replaceMatrixDomainsAtoms(curnode.getChild(0));
	        if(nr!=null) {
	            return new NodeReplacement(new OrVector(nr.current_node));
	        }
	        
	        //  Collect size of domain of comprehensions
	        long size=1;
	        
	        ASTNode comp=curnode.getChild(0);
	        
	        for(int i=0; i<comp.getChild(1).numChildren() && size<=threshold; i++) {
	            ASTNode d=comp.getChild(1).getChild(i).getChild(1);  // Get domain from ComprehensionForall
	            size=size*estimateDomainSize(d);
	        }
	        
	        if(size>threshold) {
	            //  Turn it into a set of decision variables. 
	            ASTNode newcts=new And(comp.getChild(0), comp.getChild(2));
	            
	            for(int i=0; i<comp.getChild(1).numChildren(); i++) {
                    ASTNode compforall=comp.getChild(1).getChild(i);
                    
                    if(compforall.getChild(1).getCategory()>ASTNode.Constant) {
                        //   If the domain contains other quantifier vars from the left, then
                        //   bail out. Cannot handle this case yet. 
                        return null;
                    }
                    
                    ASTNode aux=m.global_symbols.newAuxiliaryVariable(compforall.getChild(1).copy());
                    
                    ReplaceASTNode r = new ReplaceASTNode(compforall.getChild(0), aux);
                    
                    newcts=r.transform(newcts);
                }
                
                return new NodeReplacement(newcts);
	        }
	    }
	    
	    
	    //  A stack of existential quantifiers.
	    /*if(curnode instanceof ExistsExpression) {
	        ArrayList<ASTNode> doms=new ArrayList<ASTNode>();
	        doms.add(curnode.getChild(1));
	        
	        ASTNode cur=curnode.getChild(2);
	        while(cur instanceof ExistsExpression) {
	            doms.add(cur.getChild(1));
	            cur=cur.getChild(2);
	            
	            if(cur instanceof Implies && cur.getChild(0).getCategory()<=ASTNode.Quantifier) {
	                cur=cur.getChild(1);   //  Go inside a guard using implication.
	            }
	        }
	    }*/
	    
	    return null;
	}
	
	private long estimateDomainSize(ASTNode a) {
	    if(a.getCategory()==ASTNode.Constant) {
	        return Intpair.numValues(a.getIntervalSet());
	    }
	    
	    Intpair bnds=a.getBounds();  //  Poor approximation.
	    return bnds.upper-bnds.lower+1;
	}
}
