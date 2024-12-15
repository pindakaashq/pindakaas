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

//  When a constraint needs to be transformed quite drastically to work with
//  bound variables in Minion, it is dealt with here. 
//  Others (e.g. Alldiff) that just need to change the name are dealt with during output. 

public class TransformForBoundVars extends TreeTransformerBottomUp
{
    public TransformForBoundVars(Model _m) {
        super(_m);
    }
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof AtMost || curnode instanceof AtLeast)
        {
            // Will be represented as occurrenceleq/occurrencegeq in Minion that don't take bound variables. 
            // atleast(v, occ, val)
            if(curnode.getChild(0) instanceof CompoundMatrix) {
                boolean isBound=false;
                for(int i=1; i<curnode.getChild(0).numChildren(); i++) {
                    if(curnode.getChild(0).getChild(i).exceedsBoundThreshold()) {
                        isBound=true;
                        break;
                    }
                }
                if(isBound) {
                    ArrayList<ASTNode> tosum=new ArrayList<ASTNode>();
                    for(int i=1; i<curnode.getChild(0).numChildren(); i++) {
                        tosum.add(new Equals(curnode.getChild(0).getChild(i), curnode.getChild(2)));
                    }
                    
                    if(curnode instanceof AtMost) {
                        return new NodeReplacement(new LessEqual(new WeightedSum(tosum), curnode.getChild(1)));
                    }
                    else {
                        return new NodeReplacement(new LessEqual(curnode.getChild(1), new WeightedSum(tosum)));
                    }
                    
                }
            }
        }
        
        if(curnode instanceof Table || curnode instanceof NegativeTable) {
            if(curnode.getChild(0) instanceof CompoundMatrix) {
                boolean isBound=false;
                for(int i=1; i<curnode.getChild(0).numChildren(); i++) {
                    if(curnode.getChild(0).getChild(i).exceedsBoundThreshold()) {
                        isBound=true;
                        break;
                    }
                }
                
                if(isBound) {
                    ASTNode table=curnode.getChildConst(1);
                    
                    // Write out the table constraint explicitly. 
                    ArrayList<ASTNode> or=new ArrayList<ASTNode>();
                    
                    for(int i=1; i<table.numChildren(); i++) {
                        ArrayList<ASTNode> andlist=new ArrayList<ASTNode>();
                        
                        for(int j=1; j<curnode.getChild(0).numChildren(); j++) {
                            andlist.add(new Equals(curnode.getChild(0).getChild(j), table.getChild(i).getChild(j)));
                        }
                        
                        or.add(new And(andlist));
                    }
                    
                    if(curnode instanceof Table) {
                        return new NodeReplacement(new Or(or));
                    }
                    else {
                        return new NodeReplacement(new Negate(new Or(or)));
                    }
                    
                }
            }
        }
        
        if(curnode instanceof GlobalCard) {
            if(curnode.getChild(0) instanceof CompoundMatrix) {
                boolean isBound=false;
                for(int i=1; i<curnode.getChild(0).numChildren(); i++) {
                    if(curnode.getChild(0).getChild(i).exceedsBoundThreshold()) {
                        isBound=true;
                        break;
                    }
                }
                
                if(isBound) {
                    // Decompose, one ct per value.
                    ArrayList<ASTNode> cts=new ArrayList<ASTNode>();
                    
                    for(int i=1; i<curnode.getChild(1).numChildren(); i++) {
                        ASTNode val=curnode.getChild(1).getChild(i);
                        ASTNode occvar=curnode.getChild(2).getChild(i);
                        
                        // Sum the occurrences of val in the target vars.
                        ArrayList<ASTNode> sum=new ArrayList<ASTNode>();
                        for(int j=1; j<curnode.getChild(0).numChildren(); j++) {
                            sum.add(new Equals(curnode.getChild(0).getChild(j), val));
                        }
                        
                        cts.add(new Equals(new WeightedSum(sum), occvar));
                    }
                    
                    return new NodeReplacement(new And(cts));
                }
            }
        }
        
        if(curnode instanceof Mapping) {
            // Need to flatten to turn it into a Table. 
            // Then it will be dealt with by the table case above. 
            ASTNode aux=m.global_symbols.newAuxHelper(curnode);
            
            Intpair varbounds=curnode.getChild(0).getBounds();
            
            ArrayList<ASTNode> cm=new ArrayList<ASTNode>();
            for(long val=varbounds.lower; val<=varbounds.upper; val++) {
                if( ((Mapping)curnode).map.containsKey(val)) {
                    ArrayList<ASTNode> innercm=new ArrayList<ASTNode>();
                    innercm.add(NumberConstant.make(val));
                    innercm.add(NumberConstant.make(((Mapping)curnode).map.get(val)));
                    
                    cm.add(new CompoundMatrix(innercm));
                }
                else {
                    ArrayList<ASTNode> innercm=new ArrayList<ASTNode>();
                    innercm.add(NumberConstant.make(val));
                    innercm.add(NumberConstant.make(((Mapping)curnode).defaultval));
                    
                    cm.add(new CompoundMatrix(innercm));
                }
            }
            
            ArrayList<ASTNode> vars=new ArrayList<ASTNode>();
            vars.add(curnode.getChild(0));
            vars.add(aux);
            
            ASTNode tab=new Table(m, new CompoundMatrix(vars), new CompoundMatrix(cm));
            
            // Recursively use this class to transform the table into something else. 
            TransformForBoundVars tfbv=new TransformForBoundVars(m);
            tab=tfbv.transform(tab);
            
            return new NodeReplacement(aux, null, tab);
        }
        
        return null;
    }
}

