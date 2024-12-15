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
import java.util.HashSet;

import savilerow.expression.*;
import savilerow.model.Model;

//  Add an implied sum constraint(s) to allDiff and GCC constraints to feed into AC-CSE.

public class TransformAlldiffGCCSum extends TreeTransformerBottomUpNoWrapper
{
    private HashSet<ASTNode> impliedCons;   //  The set of introduced (implied) constraints. 
    
    public TransformAlldiffGCCSum(Model _m) { 
        super(_m);
        impliedCons=new HashSet<ASTNode>();
    }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof AllDifferent && curnode.getParent().inTopAnd() && curnode.getChild(0) instanceof CompoundMatrix && !(curnode.getParent() instanceof Tag))
        {
            setupFF();
            Intpair p=fordFulkerson(curnode);
            
            ASTNode newcon;
            if(p==null) {
                return new NodeReplacement(new BooleanConstant(false));
            }
            
            TransformNormalise tn=new TransformNormalise(m);
            TransformSimplify ts=new TransformSimplify();
            
            ArrayList<ASTNode> ch=curnode.getChild(0).getChildren(1);
            if(p.lower==p.upper) {
                newcon=new Equals(NumberConstant.make(p.lower), new WeightedSum(ch));
                impliedCons.add(tn.transform(ts.transform(newcon.copy())));
            }
            else {
                ASTNode c1=new LessEqual(NumberConstant.make(p.lower), new WeightedSum(ch));
                ASTNode c2=new LessEqual(new WeightedSum(ch), NumberConstant.make(p.upper));
                impliedCons.add(tn.transform(ts.transform(c1.copy())));
                impliedCons.add(tn.transform(ts.transform(c2.copy())));
                newcon=new And(c1, c2);
            }
            
            return new NodeReplacement(new And(new Tag(curnode), newcon));
            
            // The old method.
            /*
            ArrayList<ASTNode> ch=curnode.getChild(0).getChildren(1);
            
            if(ch.size()<=2) {
                // Actually a not-equal constraint. Don't add the implied sum. 
                return null;
            }
            
            // Upper bound sum. 
            ArrayList<Long> ub=new ArrayList<Long>();
            ArrayList<Long> lb=new ArrayList<Long>();
            
            for(int i=0; i<ch.size(); i++) {
                Intpair a=ch.get(i).getBounds();
                ub.add(a.upper);
                lb.add(a.lower);
            }
            
            // Upper bound sum. 
            Collections.sort(ub);
            Collections.sort(lb);
            
            // 'Enforce' alldiff by not allowing equal values, make it always increasing (lower bounds) 
            for(int i=0; i<lb.size()-1; i++) {
                if(lb.get(i)>=lb.get(i+1)) lb.set(i+1, lb.get(i)+1);
            }
            
            // Same for upper bounds. Traverse list backwards and make it always decreasing. 
            for(int i=ub.size()-1; i>0; i--) {
                if(ub.get(i)<=ub.get(i-1)) ub.set(i-1, ub.get(i)-1);
            }
            
            // Just sum the lists. 
            long upperbound=0, lowerbound=0;
            for(int i=0; i<lb.size(); i++) {
                upperbound=upperbound+ub.get(i);
                lowerbound=lowerbound+lb.get(i);
            }
            
            //System.out.println("lowerbound: "+lowerbound+" upperbound: "+upperbound+" lblist:"+lb+ " ublist:"+ub);
            ASTNode newcon;
            if(lowerbound>upperbound) {
                return new NodeReplacement(new BooleanConstant(false));
            }
            if(lowerbound==upperbound) {
                newcon=new Equals(NumberConstant.make(lowerbound), new WeightedSum(ch));
            }
            else {
                newcon=new And(
                    new LessEqual(NumberConstant.make(lowerbound), new WeightedSum(ch)), 
                    new LessEqual(new WeightedSum(ch), NumberConstant.make(upperbound)));
            }
            //System.out.println("Adding new constraint:"+newcon);
            
            return new NodeReplacement(new And(new Tag(curnode), newcon));
            */
        }
        
        //   GCC sum derived in a very similar way as AllDifferent.
        if(curnode instanceof GlobalCard && curnode.getParent().inTopAnd() && !(curnode.getParent() instanceof Tag) 
	        && curnode.getChild(0) instanceof CompoundMatrix 
	        && curnode.getChild(1) instanceof CompoundMatrix 
	        && curnode.getChild(2) instanceof CompoundMatrix)
        {
            ArrayList<ASTNode> target=curnode.getChild(0).getChildren(1);
            
            if(curnode.getChild(1).getCategory() == ASTNode.Constant) {
                
                setupFF();
                Intpair p=fordFulkerson(curnode);
                
                TransformNormalise tn=new TransformNormalise(m);
                TransformSimplify ts=new TransformSimplify();
                
                ASTNode newcon;
                if(p==null) {
                    return new NodeReplacement(new BooleanConstant(false));
                }
                if(p.lower==p.upper) {
                    newcon=new Equals(NumberConstant.make(p.lower), new WeightedSum(target));
                    impliedCons.add(tn.transform(ts.transform(newcon.copy())));
                }
                else {
                    ASTNode c1=new LessEqual(NumberConstant.make(p.lower), new WeightedSum(target));
                    ASTNode c2=new LessEqual(new WeightedSum(target), NumberConstant.make(p.upper));
                    impliedCons.add(tn.transform(ts.transform(c1.copy())));
                    impliedCons.add(tn.transform(ts.transform(c2.copy())));
                    newcon=new And(c1, c2);
                }
                return new NodeReplacement(new And(new Tag(curnode), newcon));
                
                
                // The old method.
                /*
                // Unless we know the values we are dealing with, we can't generate the sum on 
                // the target variables. 
                
                // Get the max cardinality of each value. This will be used as an upper
                // bound on the number of occurrences of each value in the ub and lb lists. 
                
                ArrayList<Long> maxcard=new ArrayList<Long>();
                ArrayList<Long> vals_long=new ArrayList<Long>();
                for(int i=0; i<occs.size(); i++) {
                    maxcard.add(occs.get(i).getBounds().upper);
                    vals_long.add(vals.get(i).getValue());
                }
                
                // Upper bound sum. 
                ArrayList<Long> ub=new ArrayList<Long>();
                ArrayList<Long> lb=new ArrayList<Long>();
                
                for(int i=0; i<target.size(); i++) {
                    Intpair a=target.get(i).getBounds();
                    ub.add(a.upper);
                    lb.add(a.lower);
                }
                
                // Upper bound sum. 
                Collections.sort(ub);
                Collections.sort(lb);
                
                // 'Enforce' GCC by not allowing equal values in some cases, make it increasing (lower bounds) 
                for(int i=0; i<lb.size(); i++) {
                    
                    // Make it non-decreasing first. 
                    if(i>0 && lb.get(i-1)>lb.get(i)) lb.set(i, lb.get(i-1));
                    
                    int value_index=vals_long.indexOf(lb.get(i));
                    
                    if(value_index>-1) {
                        // There is a constraint on this value. 
                        // Count back down the array for the number of occurrences of the current value (occs_val) 
                        // From i backwards.
                        
                        int occs_val=0;
                        for(int j=i; j>=0 && lb.get(j)==lb.get(i); j--) occs_val++;
                        
                        if(occs_val>maxcard.get(value_index)) {
                            assert occs_val-maxcard.get(value_index)==1;
                            
                            lb.set(i, lb.get(i)+1);  // Move on to the next value. 
                            
                            // Now need to check index i again because the value has changed.
                            i--;
                        }
                        
                    }
                }
                
                // 'Enforce' GCC by not allowing equal values in some cases, make it decreasing (upper bounds) 
                for(int i=ub.size()-1; i>=0; i--) {
                    // Make it non-increasing first. 
                    if( i+1 < ub.size() && ub.get(i)>ub.get(i+1)) ub.set(i, ub.get(i+1));
                    
                    int value_index=vals_long.indexOf(ub.get(i));
                    
                    if(value_index>-1) {
                        // There is a constraint on this value. 
                        // Count back down the array for the number of occurrences of the current value (occs_val). 
                        // From i forwards. 
                        
                        int occs_val=0;
                        for(int j=i; j<ub.size() && ub.get(j)==ub.get(i); j++) occs_val++;
                        
                        if(occs_val>maxcard.get(value_index)) {
                            assert occs_val-maxcard.get(value_index)==1;
                            
                            ub.set(i, ub.get(i)-1);  // Move on to the next value.
                            
                            // Now need to check index i again because the value has changed.
                            i++;
                        }
                        
                    }
                }
                
                
                // Just sum the lists. 
                long upperbound=0, lowerbound=0;
                for(int i=0; i<lb.size(); i++) {
                    upperbound=upperbound+ub.get(i);
                    lowerbound=lowerbound+lb.get(i);
                }
                System.out.println("lowerbound: "+lowerbound+" upperbound: "+upperbound+" lblist:"+lb+ " ublist:"+ub);
                ASTNode newcon;
                if(lowerbound>upperbound) {
                    return new NodeReplacement(new BooleanConstant(false));
                }
                if(lowerbound==upperbound) {
                    newcon=new Equals(NumberConstant.make(lowerbound), new WeightedSum(target));
                }
                else {
                    newcon=new And(
                        new LessEqual(NumberConstant.make(lowerbound), new WeightedSum(target)), 
                        new LessEqual(new WeightedSum(target), NumberConstant.make(upperbound)));
                }
                return new NodeReplacement(new And(new Tag(curnode), newcon));*/
            }
        }
        return null;
    }
    
    //   Following AC-CSE, remove the implied constraints that have not been changed by AC-CSE.
    public void removeImpliedConstraints() {
        assert m.constraints instanceof Top;
        if(m.constraints.getChild(0) instanceof And) {
            removeImpliedConstraints2(m.constraints.getChild(0));
        }
    }
    
    private void removeImpliedConstraints2(ASTNode and) {
        for(int i=0; i<and.numChildren(); i++) {
            if(and.getChild(i) instanceof And) {
                removeImpliedConstraints2(and.getChild(i));  // recurse
            }
            if(impliedCons.contains(and.getChild(i))) {
                and.setChild(i, new BooleanConstant(true));
            }
        }
    }
    
    //  Min-cost max flow formulation of alldiff and gcc to get upper/lower bound. 
    
    // -1 is source, connected to all value nodes via edge with capacity ub, lower bound lb. 
    // Each value is connected to any variable where it is in domain, by edge with capacity 1. 
    // Each variable is connected to the sink -2 
    
    ArrayList<Integer> augpath;
    
    ArrayList<Integer> lb;   //  Lower and upper bound on each value, indexed by value-valmin.
    ArrayList<Integer> ub;
    ArrayList<Integer> occs;
    
    ArrayList<Integer> varvalmatch;   //  Map from variables to values or valmin-1.
    
    ArrayList<ArrayList<Integer>> valadjlist;   //  Values to variables adjacency list.
    
    int valmin;
    int valmax; 
    int numvars;
    
    //  For Bellman-Ford
    ArrayList<Integer> prev;
    ArrayList<Integer> distance;
    
    void setupFF() {
       augpath=new ArrayList<Integer>();
       lb=new ArrayList<Integer>();
       ub=new ArrayList<Integer>();
       occs=new ArrayList<Integer>();
       valadjlist=new ArrayList<ArrayList<Integer>>();
       varvalmatch=new ArrayList<Integer>();
       prev=new ArrayList<Integer>();
       distance=new ArrayList<Integer>();
    }
    
    Intpair fordFulkerson(ASTNode curnode) {
        augpath.clear();
        lb.clear();
        ub.clear();
        valadjlist.clear();
        varvalmatch.clear();
        valmin=Integer.MAX_VALUE;
        valmax=Integer.MIN_VALUE;
        
        ArrayList<ASTNode> vars=curnode.getChild(0).getChildren(1);
        numvars=vars.size();
        
        //  Find minimum and maximum values. 
        for(int i=0; i<vars.size(); i++) {
            Intpair bnds=vars.get(i).getBounds();
            if(bnds.lower < valmin) valmin=(int)bnds.lower;
            if(bnds.upper > valmax) valmax=(int)bnds.upper;
        }
        
        // Construct valadjlist
        for(int i=valmin; i<=valmax; i++) {
            valadjlist.add(new ArrayList<Integer>());
        }
        
        for(int i=0; i<vars.size(); i++) {
            if(vars.get(i) instanceof Identifier) {
                ASTNode dom = ((Identifier) vars.get(i)).getDomain();
                ArrayList<Intpair> values=dom.getIntervalSet();
                
                for(int j=0; j<values.size(); j++) {
                    Intpair p=values.get(j);
                    for(int k=(int)p.lower; k<=p.upper; k++) {
                        valadjlist.get(k-valmin).add(i);
                    }
                }
            }
            else {
                Intpair p=vars.get(i).getBounds();
                for(int k=(int)p.lower; k<=p.upper; k++) {
                    valadjlist.get(k-valmin).add(i);
                }
            }
        }
        
        for(int i=0; i<vars.size(); i++) {
            varvalmatch.add(valmin-1);
        }
        
        if(curnode instanceof AllDifferent) {
            for(int i=valmin; i<=valmax; i++) {
                lb.add(0);
                ub.add(1);
                occs.add(0);
            }
        }
        else {
            assert curnode instanceof GlobalCard;
            for(int val=valmin; val<=valmax; val++) {
                lb.add(0);
                ub.add(numvars);
                occs.add(0);
                
                // Find the value in the values matrix
                for(int i=1; i<curnode.getChild(1).numChildren(); i++) {
                    if(val==curnode.getChild(1).getChild(i).getValue()) {
                        Intpair p=curnode.getChild(2).getChild(i).getBounds();
                        lb.set(lb.size()-1, (int)p.lower);
                        ub.set(ub.size()-1, (int)p.upper);
                    }
                }
            }
        }
        
        int flowsize=0;
        
        ////////////////////////////////////////////////////////////////////////
        //  
        //  Establish the lower bounds. 
        //  Numbering of vertices is source (0), sink (1), 2..numvars+1 for variables,
        //  numvars+2 to (valmax-valmin+1)+numvars+1  for the values. 
        for(int i=valmin; i<=valmax; i++) {
            while(lb.get(i-valmin) > occs.get(i-valmin)) {
                // initialise distance and prev
                distance.clear();
                prev.clear();
                for(int j=0; j<2+numvars+(valmax-valmin+1); j++) {
                    distance.add(Integer.MAX_VALUE);
                    prev.add(Integer.MIN_VALUE);
                }
                distance.set(i-valmin+numvars+2, 0);
                
                bellmanFord(i-valmin+numvars+2, true);  // The source is the value node.
                boolean pathfound=extractPath(i-valmin+numvars+2, 1);  //  Get the path from prev. 
                
                if(pathfound) {
                    augmentBF();
                    flowsize++;
                }
                else {
                    return null;   //  Constraint unsatisfiable.
                }
            }
        }
        
        //  Complete the assignment.
        
        while(flowsize < numvars) {
            // initialise distance and prev
            distance.clear();
            prev.clear();
            for(int j=0; j<2+numvars+(valmax-valmin+1); j++) {
                distance.add(Integer.MAX_VALUE);
                prev.add(Integer.MIN_VALUE);
            }
            distance.set(0, 0);
            
            bellmanFord(0, true);
            boolean pathfound=extractPath(0, 1);  // Source to sink 
            
            if(pathfound) {
                augmentBF();
                flowsize++;
            }
            else {
                return null;   //  Constraint unsatisfiable.
            }
        }
        
        Intpair ret=new Intpair(0,0);
        for(int i=0; i<varvalmatch.size(); i++) {
            ret.lower=ret.lower+varvalmatch.get(i);
        }
        
        //  Now do same for upper bound.
        //  First clear varvalmatch and occs.
        for(int i=0; i<numvars; i++) {
            varvalmatch.set(i, valmin-1);
        }
        for(int i=valmin; i<=valmax; i++) {
            occs.set(i-valmin, 0);
        }
        flowsize=0;
        
        for(int i=valmin; i<=valmax; i++) {
            while(lb.get(i-valmin) > occs.get(i-valmin)) {
                // initialise distance and prev
                distance.clear();
                prev.clear();
                for(int j=0; j<2+numvars+(valmax-valmin+1); j++) {
                    distance.add(Integer.MAX_VALUE);
                    prev.add(Integer.MIN_VALUE);
                }
                distance.set(i-valmin+numvars+2, 0);
                
                bellmanFord(i-valmin+numvars+2, false);  // The source is the value node.
                boolean pathfound=extractPath(i-valmin+numvars+2, 1);  //  Get the path from prev. 
                
                if(pathfound) {
                    augmentBF();
                    flowsize++;
                }
                else {
                    return null;   //  Constraint unsatisfiable.
                }
            }
        }
        
        while(flowsize < numvars) {
            // initialise distance and prev
            distance.clear();
            prev.clear();
            for(int j=0; j<2+numvars+(valmax-valmin+1); j++) {
                distance.add(Integer.MAX_VALUE);
                prev.add(Integer.MIN_VALUE);
            }
            distance.set(0, 0);
            
            bellmanFord(0, false);
            boolean pathfound=extractPath(0, 1);  // Source to sink 
            
            if(pathfound) {
                augmentBF();
                flowsize++;
            }
            else {
                return null;   //  Constraint unsatisfiable.
            }
        }
        
        for(int i=0; i<varvalmatch.size(); i++) {
            ret.upper=ret.upper+varvalmatch.get(i);
        }
        
        return ret;
    }
    
    // The Bellman Ford algorithm on the residual graph.
    
    boolean bfflag;
    
    void checkUpdateEdge(int a, int b, int cost) {
        //  check and update the edge (a,b) 
        //  Check no wrap around before addition. 
        if(distance.get(a)<Integer.MAX_VALUE && distance.get(a)+cost < distance.get(b)) {
            distance.set(b, distance.get(a)+cost);
            prev.set(b, a);
            bfflag=true;
        }
    }
    
    //  minimise is true if we are minimising the sum. False to maximise.
    void bellmanFord(int source, boolean minimise) {
        int numvertices=2+numvars+(valmax-valmin+1);
        
        // Loop to quiescence.
        for(int iteration=1; iteration<numvertices; iteration++) {
            bfflag=false;
            // Iterate over the edges, updating distance and prev.
            
            // Source to values.
            for(int val=valmin; val<=valmax; val++) {
                //  If the flow for this value is less than its upper limit, we can take this edge. 
                if(occs.get(val-valmin)<ub.get(val-valmin)) {
                    checkUpdateEdge(0, numvars+2+val-valmin, 0);
                }
            }
            
            // Values to source.
            for(int val=valmin; val<=valmax; val++) {
                //  If the flow for this value is greater than its lower limit, we can reverse the flow from the source.
                if(occs.get(val-valmin)>lb.get(val-valmin)) {
                    checkUpdateEdge(numvars+2+val-valmin, 0, 0);
                }
            }
            
            // Values to variables.
            for(int val=valmin; val<=valmax; val++) {
                ArrayList<Integer> adjacent=valadjlist.get(val-valmin);
                
                for(int i=0; i<adjacent.size(); i++) {
                    int var=adjacent.get(i);
                    // If the variable is not already assigned to this value, then we can take this edge. 
                    if(varvalmatch.get(var) != val) {
                        //  This edge has a cost of val-valmin, i.e. just the value normalised to 0.
                        int cost=minimise? (val-valmin) : (valmax-val);
                        checkUpdateEdge(val-valmin+numvars+2, var+2,  cost);
                    }
                }
            }
            
            //  From variables.
            for(int var=0; var<numvars; var++) {
                // Reverse flow on an edge from a value.
                if(varvalmatch.get(var) != valmin-1) {
                    int val=varvalmatch.get(var);
                    int cost=minimise? -(val-valmin) : -(valmax-val);
                    checkUpdateEdge(var+2, val-valmin+numvars+2, cost);
                }
                else {
                    // To sink.
                    checkUpdateEdge(var+2, 1, 0);
                }
            }
            
            //  From sink. 
            for(int var=0; var<numvars; var++) {
                if(varvalmatch.get(var) != valmin-1) {
                    checkUpdateEdge(1, var+2, 0);
                }
            }
            
            if(!bfflag) {
                // No updates this iteration. Reached a fixpoint.
                break;
            }
        }
    }
    
    String printVertex(int v) {
        if(v==0) return "s";
        else if(v==1) return "t";
        else if(v>1 && v<2+numvars) {
            return "x"+(v-2);
        }
        else if(v>=2+numvars && v<2+numvars+valmax-valmin+1) {
            return String.valueOf(v-2-numvars+valmin);
        }
        else {
            return "Node out of range:"+v;
        }
    }
    
    // Part of Bellman-Ford, extract the path from prev.
    boolean extractPath(int start, int end) {
        augpath.clear();
        int cur=end;
        while(cur!=start) {
            augpath.add(cur);
            cur=prev.get(cur);
            if(cur==Integer.MIN_VALUE) {
                return false;
            }
        }
        augpath.add(start);
        return true;
    }
    
    //  Augpath for Bellman-Ford --- slightly different numbering scheme. 
    void augmentBF() {
        //System.out.println("Applying augpath:"+augpath);
        for(int i=augpath.size()-1; i>0; i--) {
            int cur=augpath.get(i)-2;
            int next=augpath.get(i-1)-2;
            if(cur >= numvars && cur < numvars+(valmax-valmin+1) && next >=0 && next < numvars) {
                if(varvalmatch.get(next)!=valmin-1) {
                    int oldval=varvalmatch.get(next);
                    occs.set(oldval-valmin, occs.get(oldval-valmin)-1);
                }
                
                varvalmatch.set(next, cur-numvars+valmin);
                occs.set(cur-numvars, occs.get(cur-numvars)+1);
            }
        }
        //System.out.println("varvalmatch:"+varvalmatch);
    }    
}

