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

//  Turn alldifferent_except into a GCC.

public class TransformAlldiffExcept extends TreeTransformerBottomUp
{
    public TransformAlldiffExcept(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof AllDifferentExcept)
        {
            ASTNode matrix=curnode.getChild(0);
            assert matrix instanceof CompoundMatrix;
            ArrayList<Intpair> bnds=matrix.getIntervalSetExp();
            
            long specialval=curnode.getChild(1).getValue();
            
            if(! Intpair.contains(bnds, specialval)) {
                return new NodeReplacement(new AllDifferent(curnode.getChild(0)));
            }
            
            ArrayList<ASTNode> mat=new ArrayList<ASTNode>();
            ArrayList<ASTNode> occs=new ArrayList<ASTNode>();
            
            for(int intidx=0; intidx<bnds.size(); intidx++) {
                Intpair bnd=bnds.get(intidx);
                for(long i=bnd.lower; i<=bnd.upper; i++) {
                    if(i!=specialval) {
                        mat.add(NumberConstant.make(i));
                        occs.add(m.global_symbols.newAuxiliaryVariable(0,matrix.numChildren()-1));
                    }
                }
            }
            ASTNode vals=CompoundMatrix.make(mat);
            
            ASTNode occurrences=CompoundMatrix.make(occs);
            ASTNode new_constraint=new GlobalCard(matrix, vals, occurrences);
            
            // In this context, bound every cardinality variable to 0..1
            ArrayList<ASTNode> bound_cts=new ArrayList<ASTNode>(occs.size());
            for(int i=0; i<occs.size(); i++) {
                bound_cts.add(new InSet(occs.get(i), new IntegerDomainConcrete(0,1)));
            }
            
            //  Constraints bounding the occurrence variables go here, GCC goes
            //  at the top level. If we are in the top level conjunction, the 
            //  occs variables should be immediately pruned to 0..1.
            return new NodeReplacement(new And(bound_cts), null, new_constraint);
        }
        return null;
    }
}

