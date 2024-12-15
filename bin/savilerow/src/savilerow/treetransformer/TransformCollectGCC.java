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
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;

import savilerow.expression.*;
import savilerow.model.Model;

// Collect At-most and at-least into GCC. 
// Requires all at-least and at-most to contain only matrix literals. 

public class TransformCollectGCC extends TreeTransformerBottomUpNoWrapper
{
    public TransformCollectGCC(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof And)
        {
            ArrayList<ASTNode> new_constraints=new ArrayList<ASTNode>();
            ArrayList<ASTNode> unchanged_constraints=new ArrayList<ASTNode>(curnode.numChildren());
            
            ArrayList<Integer> idx_cons=new ArrayList<Integer>(curnode.numChildren());
            
            ArrayList<ArrayList<ASTNode>> scopes=new ArrayList<ArrayList<ASTNode>>(curnode.numChildren());
            
            for(int i=0; i<curnode.numChildren(); i++) {
                ASTNode cur=curnode.getChild(i);
                
                if(cur instanceof AtLeast || cur instanceof AtMost) {
                    idx_cons.add(i);
                    
                    ASTNode scope=cur.getChild(0);
                    assert scope instanceof CompoundMatrix || scope instanceof EmptyMatrix;
                    ArrayList<ASTNode> sc=scope.getChildren(1);
                    
                    // Sort by hashcode
                    class cmpastnode implements Comparator<ASTNode> {
                        public int compare(ASTNode x, ASTNode y) {
                            int xhash=x.hashCode();
                            int yhash=y.hashCode();
                            if(xhash < yhash) {
                                return -1;
                            }
                            else if(xhash == yhash) {
                                return 0;
                            }
                            else {
                                return 1;
                            }
                        }
                    }
                    cmpastnode cmp1=new cmpastnode();
                    
                    Collections.sort(sc, cmp1);
                    
                    scopes.add(sc);
                }
                else {
                    unchanged_constraints.add(curnode.getChild(i));
                }
            }
            
            boolean[] collected=new boolean[curnode.numChildren()];  // avoid a constraint being collected more than once. 
            
            for(int i=0; i<idx_cons.size(); i++) {
                int idx=idx_cons.get(i);
                
                if(collected[idx]) {  // This one has already been collected into a gcc.
                    continue;
                }
                
                ASTNode constraint=curnode.getChild(idx);
                
                ArrayList<ASTNode> sc=scopes.get(i);
                
                HashMap<Long, Long> lowerbounds=new HashMap<Long, Long>();
                HashMap<Long, Long> upperbounds=new HashMap<Long, Long>();
                
                update_bounds(constraint, lowerbounds, upperbounds);
                
                collected[idx]=true;
                
                // Now iterate forward for any other constraints with the same scope.
                
                for(int j=i+1; j<idx_cons.size(); j++) {
                    if(scopes.get(j).equals(sc)) {
                        collected[idx_cons.get(j)]=true;
                        
                        ASTNode constraint2=curnode.getChild(idx_cons.get(j));
                        
                        update_bounds(constraint2, lowerbounds, upperbounds);
                    }
                }
                
                // Tidy up lowerbounds and upperbounds so each has an entry every relevant value. 
                
                for(long val : lowerbounds.keySet()) {
                    if(! upperbounds.containsKey(val)) {
                        upperbounds.put(val, (long)sc.size());
                    }
                }
                
                for(long val : upperbounds.keySet()) {
                    if(! lowerbounds.containsKey(val)) {
                        lowerbounds.put(val, 0L);
                    }
                }
                
                // Construct the new GCC constraint. 
                ASTNode target=CompoundMatrix.make(sc);
                
                if(lowerbounds.size()>1) {
                    // Only make the GCC if there are two or more values involved. 
                    
                    ArrayList<ASTNode> vals=new ArrayList<ASTNode>();
                    ArrayList<ASTNode> cards=new ArrayList<ASTNode>();
                    
                    for(long val : lowerbounds.keySet()) {
                        vals.add(NumberConstant.make(val));
                        
                        // Make a new variable. 
                        
                        cards.add(m.global_symbols.newAuxiliaryVariable(lowerbounds.get(val),upperbounds.get(val)));
                    }
                    
                    ASTNode gcc=new GlobalCard(target, CompoundMatrix.make(vals), CompoundMatrix.make(cards));
                    
                    new_constraints.add(gcc);
                }
                else {
                    // Just one value. Recreate Atleast and atmost. This removes 'dominated' constraints since we create at most two new ones. 
                    for(long val : lowerbounds.keySet()) {
                        long occs=lowerbounds.get(val);
                        if(occs > 0) {
                            new_constraints.add(new Tag(new AtLeast(target, CompoundMatrix.make(NumberConstant.make(occs)), CompoundMatrix.make(NumberConstant.make(val)))));
                        }
                    }
                    
                    for(long val : upperbounds.keySet()) {
                        long occs=upperbounds.get(val);
                        if(occs < sc.size()) {
                            new_constraints.add(new Tag(new AtMost(target, CompoundMatrix.make(NumberConstant.make(occs)), CompoundMatrix.make(NumberConstant.make(val)))));
                        }
                    }
                }
            }
            
            if(new_constraints.size()>0) {
                unchanged_constraints.addAll(new_constraints);   // Should clear all parent pointers to avoid copying all the constraints.
                
                return new NodeReplacement(new And(unchanged_constraints), null, null);
            }
        }
        return null;
    }
    
    private void update_bounds(ASTNode constraint, HashMap<Long, Long> lowerbounds, HashMap<Long, Long> upperbounds) {
        for(int i=1; i<constraint.getChild(2).numChildren(); i++) {
            
            long value=constraint.getChild(2).getChild(i).getValue();
            
            long occ=constraint.getChild(1).getChild(i).getValue();
            
            if(constraint instanceof AtLeast) {
                // Add to lower bounds
                if(lowerbounds.containsKey(value)) {
                    lowerbounds.put(value, (lowerbounds.get(value)>occ ? lowerbounds.get(value) : occ));
                }
                else {
                    lowerbounds.put(value, occ);
                }
            }
            else {
                // Add to upper bounds
                if(upperbounds.containsKey(value)) {
                    upperbounds.put(value, (upperbounds.get(value)<occ ? upperbounds.get(value) : occ));
                }
                else {
                    upperbounds.put(value, occ);
                }
            }
        }
    }
}

