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

// Decompose alldiff into a set of atmost constraints, one for each value. 
// Used for SAT encoding initially 

public class TransformAlldiffToSums extends TreeTransformerBottomUpNoWrapper
{
    public TransformAlldiffToSums(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof AllDifferent && curnode.getChild(0) instanceof CompoundMatrix && curnode.getChild(0).numChildren()>3) {
            // Take the union of the intersection of the domain of each pair of variables
            // Other values (that appear in one variable) are not relevant.
            ASTNode cm=curnode.getChild(0);
            
            ArrayList<Intpair> values=new ArrayList<Intpair>();  //  values contained in two or more expressions in scope
            ArrayList<Intpair> all_values=new ArrayList<Intpair>();   //  values contained in one or more expressions in scope.
            
            for(int i=1; i<cm.numChildren(); i++) {
                ArrayList<Intpair> dom1=cm.getChild(i).getIntervalSetExp();
                
                all_values=Intpair.union(all_values, dom1);
                
                for(int j=i+1; j<cm.numChildren(); j++) {
                    ArrayList<Intpair> dom2=cm.getChild(j).getIntervalSetExp();
                    
                    values=Intpair.union(values, Intpair.intersection(dom1, dom2));
                }
            }
            
            long numValues=Intpair.numValues(all_values);
            if(numValues < cm.numChildren()-1) {
                return new NodeReplacement(new BooleanConstant(false));
            }
            
            ArrayList<ASTNode> decomp=new ArrayList<ASTNode>();
            for(Intpair p : values) {
                for(long val=p.lower; val<=p.upper; val++) {
                    ArrayList<ASTNode> scope=new ArrayList<ASTNode>(cm.numChildren()-1);
                    
                    for(int i=1; i<cm.numChildren(); i++) {
                        scope.add(new Equals(cm.getChild(i), NumberConstant.make(val)));
                    }
                    
                    if(numValues==cm.numChildren()-1) {
                        // It's a permutation. Add an equality.
                        decomp.add(new Equals(new WeightedSum(scope), NumberConstant.make(1)));
                    }
                    else {
                        //  Not a permutation. At most one of val is required. 
                        decomp.add(new LessEqual(new WeightedSum(scope), NumberConstant.make(1)));
                    }
                }
            }
            return new NodeReplacement(new And(decomp));
        }
        return null;
    }
}

