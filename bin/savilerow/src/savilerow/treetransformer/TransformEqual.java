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

//  Special-case flattener for equality between two expressions that both need
// flattening. Makes one aux variable for one 

public class TransformEqual extends TreeTransformerBottomUp
{
    public TransformEqual(Model _m, boolean _propagate) {
        super(_m);
        propagate=_propagate;
    }
    private boolean propagate;
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof Equals)
        {
            ASTNode c1=curnode.getChild(0);
            ASTNode c2=curnode.getChild(1);
            if(c1.toFlatten(propagate) && c2.toFlatten(propagate)) {
                ArrayList<Intpair> a=c1.getIntervalSetExp();
                ArrayList<Intpair> b=c2.getIntervalSetExp();
                
                if(curnode.getParent().inTopAnd()) {
                    // If top level equality
                    
                    // Intersection.
                    ArrayList<Intpair> c=Intpair.intersection(a, b);
                    
                    if(c.size()==0) {  // two expressions can't be equal.
                        return new NodeReplacement(new BooleanConstant(false));
                    }
                    if(c.size()==1 && c.get(0).lower==c.get(0).upper) { // Both expressions equal a constant.
                        return new NodeReplacement(new And(new Equals(c1, NumberConstant.make(c.get(0).upper)), 
                            new Equals(c2, NumberConstant.make(c.get(0).upper))));
                    }
                    
                    // Instead of using newAuxHelper, because we have two expressions it is done manually.
                    ASTNode auxdom=m.filt.constructDomain(c1, Intpair.makeDomain(c, c1.isRelation() || c2.isRelation()));  //  Look up stored (filtered) domain if there is one. Once for each expression.
                    auxdom=m.filt.constructDomain(c2, auxdom);
                    ASTNode auxvar=m.global_symbols.newAuxiliaryVariable(auxdom);
                    
                    m.filt.auxVarRepresentsAST(auxvar.toString(), c1);    // Associate one of the expressions with the aux variable. 
                    
                    m.global_symbols.auxVarRepresentsConstraint( auxvar.toString(), c1.toString()+" --- "+c2.toString());
                    
                    return new NodeReplacement(new And(new ToVariable(c1, auxvar.copy()), 
                        new ToVariable(c2, auxvar.copy())));
                }
                else {
                    // Not top level equality. 
                    // Can't take intersection of the two intervals. Instead take the smaller interval and extract the expression corresponding to that.
                    // Leaves a toVariable in this context, and also one toVariable at the top level to define the aux var. 
                    
                    ASTNode toExtract;
                    ASTNode other;
                    
                    if(Intpair.numValues(a) < Intpair.numValues(b)) {
                        toExtract=c1;
                        other=c2;
                    }
                    else {
                        toExtract=c2;
                        other=c1;
                    }
                    
                    ASTNode auxvar=m.global_symbols.newAuxHelper(toExtract);
                    ASTNode toplevel=new ToVariable(toExtract, auxvar);
                    
                    ASTNode repl=new ToVariable(other, auxvar);
                    
                    return new NodeReplacement(repl, null, toplevel);
                }
            }
        }
        return null;
    }
}



