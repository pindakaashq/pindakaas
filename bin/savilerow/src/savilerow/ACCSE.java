package savilerow;
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import savilerow.expression.*;
import savilerow.model.Model;

// To run after standard 'identical' CSE.
// Traverse expression tree and find common subsets between N-ary constraints.

// Identical Ands, Ors etc have already been eliminated by CSE.
// Also identical subexpressions have already been factored out of the ands, ors etc. 

// Shuold this not go before 'identical' CSE?

public class ACCSE
{
    private LinkedHashMap<PairASTNode, ArrayList<ASTNode>> exp;
    
    private HashMap<ASTNode, Long> expression_counts;    // If an expression only occurs once inside a sum, never add a pair containing that expression to exp.  
    // Contains MultiplyMappers
    
    private HashSet<ASTNode> done;   // for use when doing leave constraints in.
    
    public int numcse;
    public int countcse;
    public int totallength;
    
    private String type;   //  /\ , \/, *, +, xor
    
    boolean isPlus;  // if type.equals("+") occurred a lot so using a bool. 
    
    static boolean eagerFilterLists=false;
    
    public void flattenCSEs(Model m, String tp) {
        type=tp;
        
        isPlus=type.equals("+");
        
        // Statistics
        numcse=0;     //  Number of CSE's
        countcse=0;   //  Total number of expressions replaced with auxvar.
        totallength=0;
        
        exp=new LinkedHashMap<PairASTNode, ArrayList<ASTNode>>();
        
        expression_counts=new HashMap<ASTNode, Long>();
        
        if(CmdFlags.accse_heuristic==6) done=new HashSet<ASTNode>();   // done contains the common sets that have been processed already. 
        
        populate_expression_counts(m.constraints);   // Only does this once. Counts will go down as CSE's are eliminated but ignoring that. 
        
        populate_exp(m.constraints);
        
        ArrayList<ASTNode> new_constraints=new ArrayList<ASTNode>();
        
        //System.out.println("Initial hashtable size:"+exp.size());
        
        while( ! exp.isEmpty() ) {
            
            // Take any pair out of the hashmap and process it.
            // It is safe to take the pair out, because CSE will never re-introduce a pair
            // after it is processed. 
            // Say
            //  X Y A,   X Y Z B, X Y Z C,  W X Y D,  W X Y E
            //  Suppose we  process X Y first. 
            //  b A,  X b B,  X b C, W b D, W b E
            //  X Y <-> b
            //  All references to ANDs remaining in exp are dead.
            // Need to re-add all ANDs we make so we catch W b and X b. 
            // Also need to add the AND in the reification, in case we had done W X Y first. 
            
            // If a pair only has one thing in its list... might as well delete the pair.
            // We cannot add another instance of the same pair. WHY NOT?
            
            ArrayList<ASTNode> ls;
            
            if(CmdFlags.accse_heuristic==0) {
                Iterator<Map.Entry<PairASTNode, ArrayList<ASTNode>>> it=exp.entrySet().iterator();
                
                Map.Entry<PairASTNode, ArrayList<ASTNode>> object=it.next();
                
                it.remove();   // First in insertion order -- effectively a FIFO.
                
                ls=object.getValue();
            }
            else {   //   CmdFlags.accse_heuristic>=1
                // Iterate through exp, filter out detached things. Keep the ones with the longest & shortest list of occurrences. 
                
                Iterator<Map.Entry<PairASTNode, ArrayList<ASTNode>>> it=exp.entrySet().iterator();
                
                PairASTNode largestseen=null;
                int largestseen_size=-1;
                
                PairASTNode smallestseen=null;
                int smallestseen_size=Integer.MAX_VALUE;
                
                PairASTNode largestseencommonset=null;
                int largestseencommonset_size=-1;
                
                PairASTNode smallestseencommonset=null;
                int smallestseencommonset_size=Integer.MAX_VALUE;
                
                while(it.hasNext()) {
                    Map.Entry<PairASTNode, ArrayList<ASTNode>> object=it.next();
                    
                    PairASTNode key=object.getKey();
                    ArrayList<ASTNode> ls2=object.getValue();
                    
                    if(!eagerFilterLists) {
                        CSE.filterlist(ls2);  // updates list in place, in the hashtable.
                    }
                    
                    if(ls2.size()<=1) {
                        it.remove();     // This pair has one or 0 occurrences, so get rid of it. 
                    }
                    else {
                        if(ls2.size()<smallestseen_size) {
                            smallestseen=key;
                            smallestseen_size=ls2.size();
                        }
                        if(ls2.size()>largestseen_size) {
                            largestseen=key;
                            largestseen_size=ls2.size();
                        }
                        
                        if(CmdFlags.accse_heuristic==3 || CmdFlags.accse_heuristic==4 || CmdFlags.accse_heuristic==13 || CmdFlags.accse_heuristic==14) {
                            int csetsize;
                            if(isPlus) {
                                // Special case + because of weights. 
                                Pair<ArrayList<ASTNode>, ArrayList<Long>> p1=buildCommonSetSums(ls2);
                                csetsize=p1.getFirst().size();
                            }
                            else {
                                ArrayList<ASTNode> p1=buildCommonSet(ls2);
                                csetsize=p1.size();
                            }
                            
                            if(csetsize<smallestseencommonset_size) {
                                smallestseencommonset=key;
                                smallestseencommonset_size=csetsize;
                            }
                            if(csetsize>largestseencommonset_size) {
                                largestseencommonset=key;
                                largestseencommonset_size=csetsize;
                            }
                            
                        }
                        
                    }
                }
                
                if(exp.isEmpty()) {
                    // Bail out of the main loop.  
                    break;
                }
                
                if(CmdFlags.accse_heuristic==1  ||  CmdFlags.getUseACCSEAlt()) {
                    //  The default -- largest list seen. 
                    //  Either the heuristic value is a 1 OR we are using I-CSE for Sums and Products,
                    //  and X-CSE for conjunction and disjunction, in which case use the default heuristic
                    //  for X-CSE. 
                    ls=exp.get(largestseen); 
                    exp.remove(largestseen);
                }
                else if(CmdFlags.accse_heuristic==2) {
                    ls=exp.get(smallestseen);   // Smallest list seen.
                    exp.remove(smallestseen);
                }
                else if(CmdFlags.accse_heuristic==3) {
                    // Largest common set
                    ls=exp.get(largestseencommonset);
                    exp.remove(largestseencommonset);
                }
                else if(CmdFlags.accse_heuristic==4) {
                    // Smallest common set
                    ls=exp.get(smallestseencommonset);
                    exp.remove(smallestseencommonset);
                }
                else if(CmdFlags.accse_heuristic==5 || CmdFlags.accse_heuristic==6) {
                    //  heuristic is either 5 (random) or 6 (random+leave constraints in).
                    int choice=(int) (Math.random() * (exp.size()));
                    Iterator<Map.Entry<PairASTNode, ArrayList<ASTNode>>> itt=exp.entrySet().iterator();
                    
                    //System.out.println("Choice: "+choice+" of "+exp.size());
                    
                    while(choice>0 && itt.hasNext()) {
                        choice--;
                        itt.next();
                    }
                    
                    PairASTNode key=itt.next().getKey();
                    
                    ls=exp.get(key);
                    exp.remove(key);
                }
                
                ////////////////////////////////////////////////////////////////
                //
                //  Now the same heuristics above but with non blocking pairs first. 
                
                else if(CmdFlags.accse_heuristic==11) {
                    // heuristic is 11 (non-blocking then largest list seen)
                    PairASTNode p1=findNonBlockingPair();
                    
                    if(p1==null) {
                        ls=exp.get(largestseen);    // Largest list seen. 
                        exp.remove(largestseen);
                    }
                    else {
                        ls=exp.get(p1);
                        exp.remove(p1);
                    }
                }
                else if(CmdFlags.accse_heuristic==12) {
                    // heuristic is 12 (non-blocking then shortest list seen)
                    PairASTNode p1=findNonBlockingPair();
                    
                    if(p1==null) {
                        ls=exp.get(smallestseen);    // Smallest list seen. 
                        exp.remove(smallestseen);
                    }
                    else {
                        ls=exp.get(p1);
                        exp.remove(p1);
                    }
                }
                else if(CmdFlags.accse_heuristic==13) {
                    // heuristic is 13 (non-blocking then largest common set seen)
                    PairASTNode p1=findNonBlockingPair();
                    
                    if(p1==null) {
                        ls=exp.get(largestseencommonset);    // Largest common set 
                        exp.remove(largestseencommonset);
                    }
                    else {
                        ls=exp.get(p1);
                        exp.remove(p1);
                    }
                }
                else if(CmdFlags.accse_heuristic==14) {
                    // heuristic is 14 (non-blocking then smallest common set seen)
                    PairASTNode p1=findNonBlockingPair();
                    
                    if(p1==null) {
                        ls=exp.get(smallestseencommonset);    // Smallest common set seen. 
                        exp.remove(smallestseencommonset);
                    }
                    else {
                        ls=exp.get(p1);
                        exp.remove(p1);
                    }
                }
                else if(CmdFlags.accse_heuristic==15) {
                    // heuristic is 15 (non-blocking then random)
                    PairASTNode p1=findNonBlockingPair();
                    
                    if(p1==null) {
                        // take a random choice. 
                        int choice=(int) (Math.random() * (exp.size()));
                        Iterator<Map.Entry<PairASTNode, ArrayList<ASTNode>>> itt=exp.entrySet().iterator();
                        
                        //System.out.println("Choice: "+choice+" of "+exp.size());
                        
                        while(choice>0 && itt.hasNext()) {
                            choice--;
                            itt.next();
                        }
                        
                        p1=itt.next().getKey();
                        
                    }
                    
                    ls=exp.get(p1);
                    exp.remove(p1);
                }
                else {
                    CmdFlags.errorExit("N-ary CSE heuristic is not valid.");
                    return;    //  To stop the control flow analysis complaining.
                }
            }
            
            ////////////////////////////////////////////////////////////////////
            //
            //   
            
            if(ls.size()==1) continue;
            
            if(CmdFlags.accse_heuristic==0) {
                // Remove items from ls that are no longer connected to the root because of other CSEs being flattened
                if(!eagerFilterLists) {
                    CSE.filterlist(ls);
                }
            }
            
            // Remove duplicate refs to same object. This can happen if same pair occurs multiple times in expression.
            // Shouldn't happen with sums, max, min, and, or, parity because duplicates will be simplified away.  
            // Occurs with product. 
            
            for(int i=0; i<ls.size(); i++) {
                for(int j=i+1; j<ls.size(); j++) {
                    if(ls.get(i)==ls.get(j)) {
                        ls.set(j, ls.get(ls.size()-1));
                        ls.remove(ls.size()-1);
                        j--;
                    }
                }
            }
            
            if(ls.size()>1) {
                // Find the largest set where /all/ elements are in each conjunction in ls.
                // Largest set gives most chance of cse var being set to true... in OR case. 
                ArrayList<ASTNode> commonset;
                ArrayList<Long> commonsetweights;
                
                if(isPlus) {
                    Pair<ArrayList<ASTNode>, ArrayList<Long>> p1=buildCommonSetSums(ls);
                    commonset=p1.getFirst();
                    commonsetweights=p1.getSecond();
                }
                else {
                    commonset=buildCommonSet(ls);
                    commonsetweights=null;
                }
                
                if(CmdFlags.accse_heuristic==6) {  // If random + leave constraints in. 
                    assert type.equals("+");
                    ASTNode tmp=new WeightedSum(commonset, commonsetweights);
                    tmp=tmp.normalise();  // sort. 
                    if(done.contains(tmp)) {
                        continue;  // Bail out, do next pair. 
                    }
                }
                
                ASTNode con_inner=CommAssocFactory.makeCommAssoc(type, commonset, commonsetweights);
                
                ASTNode auxvar=m.global_symbols.newAuxHelper(con_inner);
                
                ASTNode con=new ToVariable(con_inner, auxvar);
                
                for(ASTNode a : ls) {  // Replace all instances with the aux variable.
                    int childno=a.getChildNo();
                    
                    ArrayList<ASTNode> tmp=a.getChildren();
                    ArrayList<Long> tmpweights=null;
                    if(isPlus) tmpweights=((WeightedSum)a).getWeights();
                    
                    for(int i=0; i<commonset.size(); i++) {
                        int tmpidx=tmp.indexOf(commonset.get(i));
                        tmp.remove(tmpidx);
                        if(isPlus) tmpweights.remove(tmpidx);
                    }
                    tmp.add(auxvar.copy());
                    if(isPlus) tmpweights.add(1L);
                    
                    ASTNode replace_a=CommAssocFactory.makeCommAssoc(type, tmp, tmpweights);
                    
                    if(CmdFlags.accse_heuristic!=6) {   // If NOT leaving constraints in. 
                        populate_exp(replace_a);
                        if(eagerFilterLists) {
                            unpopulate_exp(a);
                        }
                        // Replaces the expression in ls with the new one.
                        a.getParent().setChild(childno, replace_a);
                    }
                    else {
                        // Much more complicated -- copy the whole constraint containing 'a'
                        // and make the replacement in the copy. 
                        // Go up until find a relation. For example sum=constant will go up one 
                        // level because equality is a relation. 
                        // This part only works for sums. 
                        assert type.equals("+");
                        ASTNode par=a;
                        ArrayList<Integer> childnos=new ArrayList<Integer>();
                        
                        while( ! par.isRelation()) {
                            childnos.add(par.getChildNo());
                            par=par.getParent();
                        }
                        
                        ASTNode repct=par.copy();
                        
                        // Now find the sum again in repct. 
                        ASTNode sumnode=repct;
                        for(int i=childnos.size()-1; i>=0; i--) {
                            sumnode=sumnode.getChild(childnos.get(i));
                        }
                        
                        assert sumnode instanceof WeightedSum;
                        
                        // make the replacement as in the non-copying case.  
                        sumnode.getParent().setChild(childno, replace_a);
                        
                        // The new constraint is now added to the hashtable (may contain more than one sum)
                        populate_exp(repct);
                        populate_expression_counts(repct);    // since this is a brand new bit of the tree, need to count expressions as well. 
                        
                        // stitch par /\ repct into the tree. 
                        
                        ASTNode parent=par.getParent();
                        int parent_childno=par.getChildNo();
                        par.setParent(null);   // Make sure par is not copied
                        parent.setChild(parent_childno, new And(par, repct));
                    }
                }
                
                if(CmdFlags.accse_heuristic==6) {    // If leaving constraints in, add common set to 'done' set. 
                    // Again this bit only works for sum. 
                    ASTNode tmp=new WeightedSum(commonset, commonsetweights);
                    tmp=tmp.normalise();  // sort. 
                    done.add(tmp);  // Don't do the same common set again. 
                }
                
                m.global_symbols.auxVarRepresentsConstraint( auxvar.toString(), "AC-CSE-Generic-"+type+": "+ls.size()+" occurrences of: "+(con_inner.toString()));
                
                populate_exp(con);
                
                if(CmdFlags.accse_heuristic==6) {   // If leaving constraints in...
                    con=new Tag(con);  // Tag is to ensure con has a parent
                }
                
                new_constraints.add(con);
                
                numcse++;
                countcse+=ls.size();
                totallength+=ls.get(0).treesize();
            }
        }
        
        // Conjoin all the new constraints onto the top level.
        m.constraints.getChild(0).setParent(null);
        new_constraints.add(m.constraints.getChild(0));
        m.constraints.setChild(0, new And(new_constraints));
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //  Populate map from pairs to list of expressions containing the pair. 
    
    //  These methods should create a _set_ of pairs then populate lists from
    //  the set. This way it avoids putting multiple refs to the same expression into
    //  one list. 
    
    private void populate_exp(ASTNode a) {
        if(isPlus) {
            populate_exp_sum(a);
        }
        else {
            populate_exp_nonsum(a);
        }
    }
    
    private void populate_exp_sum(ASTNode a)  {
        if( a instanceof WeightedSum) {
            
            ArrayList<ASTNode> children=a.getChildren();
            ArrayList<Long> wts=((WeightedSum)a).getWeights();
            
            ArrayList<ASTNode> mapped=new ArrayList<ASTNode>();
            for(int i=0; i<children.size(); i++) {
                ASTNode a1=new MultiplyMapper(children.get(i).copy(), NumberConstant.make(wts.get(i)));
                
                //assert expression_counts.containsKey(a1);  Not true for new aux vars. 
                if( (!expression_counts.containsKey(a1)) || expression_counts.get(a1)>1L) {
                    mapped.add(a1);    /// Only add it if it occurs more than once globally, 
                    // or it is a new aux var (not in expression_counts, and guaranteed to occur more than once).
                }
            }
            
            for(int i=0; i<mapped.size(); i++) {
                for(int j=i+1; j<mapped.size(); j++) {
                    ASTNode a1=mapped.get(i);            
                    ASTNode a2=mapped.get(j);
                    
                    if(CmdFlags.accse_heuristic==6 && (((Identifier)a1.getChild(0)).isAuxiliary() || ((Identifier)a2.getChild(0)).isAuxiliary())) {
                        continue;
                    }
                    
                    if(a1.hashCode() > a2.hashCode()) {
                        ASTNode tmp=a2;
                        a2=a1;
                        a1=tmp;
                    }
                    
                    PairASTNode p=new PairASTNode(a1, a2);   
                    
                    if(exp.containsKey(p)) {
                        exp.get(p).add(a);
                    }
                    else {
                        ArrayList<ASTNode> list=new ArrayList<ASTNode>();
                        list.add(a);
                        exp.put(p, list);
                    }
                }
            }
        }
        
        for(int i=0; i<a.numChildren(); i++) {
            populate_exp_sum(a.getChild(i));
        }
    }
    
    // Anything except sum. 
    private void populate_exp_nonsum(ASTNode a)  {
        if( a.isCommAssoc() // Check it is both commutative and associative. And, Or, Times, etc
            && matches_type(a)
            && !(a.getParent() instanceof Top && a instanceof And)) {  // Exclude the top-level And.
            
            for(int i=0; i<a.numChildren(); i++) {
                for(int j=i+1; j<a.numChildren(); j++) {
                    
                    ASTNode a1=a.getChild(i).copy();            
                    ASTNode a2=a.getChild(j).copy();   // Copy so that they will not be changed and screw up the hashmap.
                    
                    if(a1.hashCode() > a2.hashCode()) {
                        ASTNode tmp=a2;
                        a2=a1;
                        a1=tmp;
                    }
                    
                    PairASTNode p=new PairASTNode(a1, a2);   
                    
                    if(exp.containsKey(p)) {
                        exp.get(p).add(a);
                    }
                    else {
                        ArrayList<ASTNode> list=new ArrayList<ASTNode>();
                        list.add(a);
                        exp.put(p, list);
                    }
                }
            }
        }
        
        for(int i=0; i<a.numChildren(); i++) {
            populate_exp_nonsum(a.getChild(i));
        }
    }
    
    
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //  AC-Expression a is about to be removed from the tree. Remove references to a from exp.
    
    private void unpopulate_exp(ASTNode a) {
        if(isPlus) {
            unpopulate_exp_sum(a);
        }
        else {
            unpopulate_exp_nonsum(a);
        }
    }
    
    private void unpopulate_exp_sum(ASTNode a)  {
        if( a instanceof WeightedSum) {
            
            ArrayList<ASTNode> children=a.getChildren();
            ArrayList<Long> wts=((WeightedSum)a).getWeights();
            
            ArrayList<ASTNode> mapped=new ArrayList<ASTNode>();
            for(int i=0; i<children.size(); i++) {
                ASTNode a1=new MultiplyMapper(children.get(i).copy(), NumberConstant.make(wts.get(i)));
                
                //assert expression_counts.containsKey(a1);  Not true for new aux vars. 
                if( (!expression_counts.containsKey(a1)) || expression_counts.get(a1)>1L) {
                    mapped.add(a1);    /// Only add it if it occurs more than once globally. 
                }
            }
            
            for(int i=0; i<mapped.size(); i++) {
                for(int j=i+1; j<mapped.size(); j++) {
                    ASTNode a1=mapped.get(i);            
                    ASTNode a2=mapped.get(j);
                    
                    if(CmdFlags.accse_heuristic==6 && (((Identifier)a1.getChild(0)).isAuxiliary() || ((Identifier)a2.getChild(0)).isAuxiliary())) {
                        continue;
                    }
                    
                    if(a1.hashCode() > a2.hashCode()) {
                        ASTNode tmp=a2;
                        a2=a1;
                        a1=tmp;
                    }
                    
                    PairASTNode p=new PairASTNode(a1, a2);   
                    
                    if(exp.containsKey(p)) {
                        //  Old, working version where the item is removed from the list. 
                        exp.get(p).remove(a);
                        if(exp.get(p).size()==0) {
                            exp.remove(p);
                        }
                    }
                }
            }
        }
        
        for(int i=0; i<a.numChildren(); i++) {
            unpopulate_exp_sum(a.getChild(i));
        }
    }
    
    private void unpopulate_exp_nonsum(ASTNode a)  {
        if( a.isCommAssoc() // Check it is both commutative and associative. And, Or, Times, etc
            && matches_type(a)
            && !(a.getParent() instanceof Top && a instanceof And)) {  // Exclude the top-level And.
            
            for(int i=0; i<a.numChildren(); i++) {
                for(int j=i+1; j<a.numChildren(); j++) {
                    
                    ASTNode a1=a.getChild(i).copy();            
                    ASTNode a2=a.getChild(j).copy();   // Copy so that they will not be changed and screw up the hashmap.
                    
                    if(a1.hashCode() > a2.hashCode()) {
                        ASTNode tmp=a2;
                        a2=a1;
                        a1=tmp;
                    }
                    
                    PairASTNode p=new PairASTNode(a1, a2);   
                    
                    if(exp.containsKey(p)) {
                        //  Old, working version where the item is removed from the list. 
                        exp.get(p).remove(a);
                        if(exp.get(p).size()==0) {
                            exp.remove(p);
                        }
                    }
                }
            }
        }
        
        for(int i=0; i<a.numChildren(); i++) {
            unpopulate_exp_nonsum(a.getChild(i));
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    
    private void populate_expression_counts(ASTNode a)  {
        if( a.isCommAssoc() // Check it is both commutative and associative. And, Or, Times, etc
            && matches_type(a)
            && !(a.getParent() instanceof Top && a instanceof And)) {  // Exclude the top-level And.
            for(int i=0; i<a.numChildren(); i++) {
                
                ASTNode b=a.getChild(i);
                
                ASTNode c=b;
                if(isPlus) c=new MultiplyMapper(b.copy(), NumberConstant.make(((WeightedSum)a).getWeight(i)));
                
                if(expression_counts.containsKey(c)) {
                    expression_counts.put(c, expression_counts.get(c)+1L);
                }
                else {
                    expression_counts.put(c, 1L);
                }
            }
        }
        
        for(int i=0; i<a.numChildren(); i++) {
            populate_expression_counts(a.getChild(i));
        }
    }
    
    private Pair<ArrayList<ASTNode>, ArrayList<Long>> buildCommonSetSums(ArrayList<ASTNode> ls) {
        ArrayList<ArrayList<ASTNode>> ah=new ArrayList<ArrayList<ASTNode>>();
        ArrayList<ArrayList<Long>> ahw=new ArrayList<ArrayList<Long>>();
        for(ASTNode list : ls) {
            ah.add(list.getChildren());
            ahw.add(((WeightedSum)list).getWeights());
        }
        
        ArrayList<ASTNode> commonset=ls.get(0).getChildren();
        ArrayList<Long> commonsetweights=((WeightedSum) ls.get(0)).getWeights();
        
        for(int i=0; i<commonset.size(); i++) {
            ASTNode a=commonset.get(i);
            long w=commonsetweights.get(i);
            
            for(int j=1; j<ls.size(); j++) {
                int a_index=ah.get(j).indexOf(a);
                if(a_index==-1  || ahw.get(j).get(a_index)!=w) {    
                    // Either the child is not there or the weight does not match. 
                    commonset.set(i, commonset.get(commonset.size()-1));
                    commonset.remove(commonset.size()-1);
                    
                    commonsetweights.set(i, commonsetweights.get(commonsetweights.size()-1));
                    commonsetweights.remove(commonsetweights.size()-1);
                    
                    i--;   // do position i again. 
                    break;
                }
                else {
                    ah.get(j).remove(a_index); // Get rid of this element so it can't match twice.
                    ahw.get(j).remove(a_index);
                }
            }
        }
        
        return new Pair<ArrayList<ASTNode>, ArrayList<Long>>(commonset, commonsetweights);
    }
    
    public static ArrayList<ASTNode> buildCommonSet(ArrayList<ASTNode> ls) {
        ArrayList<ArrayList<ASTNode>> ah=new ArrayList<ArrayList<ASTNode>>();
        for(ASTNode list : ls) {
            ah.add(list.getChildren());
        }
        
        ArrayList<ASTNode> commonset=ls.get(0).getChildren();
        
        for(int i=0; i<commonset.size(); i++) {
            ASTNode a=commonset.get(i);
            
            for(int j=1; j<ls.size(); j++) {
                int a_index=ah.get(j).indexOf(a);
                if(a_index==-1) {
                    // Either the child is not there or the weight does not match. 
                    commonset.set(i, commonset.get(commonset.size()-1));
                    commonset.remove(commonset.size()-1);
                    
                    i--;   // do position i again. 
                    break;
                }
                else {
                    ah.get(j).remove(a_index); // Get rid of this element so it can't match twice.
                }
            }
        }
        
        return commonset;
    }
    
    private PairASTNode findNonBlockingPair() {
        // If there is a non-blocking pair, return it, otherwise return null.
        
        // make a new hash table with hashsets of astnodes representing all pairs in exp
        
        HashMap<ASTNode, HashSet<ASTNode>> pairs=new HashMap<ASTNode, HashSet<ASTNode>>();
        
        Iterator<PairASTNode> itt=exp.keySet().iterator();
        while(itt.hasNext()) {
            PairASTNode pa=itt.next();
            
            // insert in both directions into pairs.
            
            if(pairs.containsKey(pa.e1)) {
                pairs.get(pa.e1).add(pa.e2);
            }
            else {
                HashSet<ASTNode> tmp=new HashSet<ASTNode>();
                tmp.add(pa.e2);
                pairs.put(pa.e1, tmp);
            }
            
            if(pairs.containsKey(pa.e2)) {
                pairs.get(pa.e2).add(pa.e1);
            }
            else {
                HashSet<ASTNode> tmp=new HashSet<ASTNode>();
                tmp.add(pa.e1);
                pairs.put(pa.e2, tmp);
            }
        }
        
        // Now search for non-blocking choices in exp. 
        Iterator<Map.Entry<PairASTNode, ArrayList<ASTNode>>> it2=exp.entrySet().iterator();
        
        while(it2.hasNext()) {
            Map.Entry<PairASTNode, ArrayList<ASTNode>> extentry=it2.next();
            
            ArrayList<ASTNode> ls=extentry.getValue();
            
            // Remove duplicate refs to same object. This can happen if same pair occurs multiple times in expression.
            // Shouldn't happen with sums, max, min, and, or, parity because duplicates will be simplified away.  
            // Occurs with product. 
            
            for(int i=0; i<ls.size(); i++) {
                for(int j=i+1; j<ls.size(); j++) {
                    if(ls.get(i)==ls.get(j)) {
                        ls.set(j, ls.get(ls.size()-1));
                        ls.remove(ls.size()-1);
                        j--;
                    }
                }
            }
            
            if(ls.size()<2) {
                // pair may be non-blocking but it also has no CSE. Continue to next pair.
                continue;
            }
            
            ArrayList<ASTNode> commonset;
            ArrayList<Long> commonsetweights;
            
            if(isPlus) {
                Pair<ArrayList<ASTNode>, ArrayList<Long>> p1=buildCommonSetSums(ls);
                commonset=p1.getFirst();
                commonsetweights=p1.getSecond();
            }
            else {
                commonset=buildCommonSet(ls);
                commonsetweights=null;
            }
            
            /// Check if anything in commonset also appears in a pair with something else outside commonset and 
            // these two appear in a constraint outside ls. This means it's blocking another CSE. 
            
            boolean blocking=false;
            
            for(int i=0; i<commonset.size() && !blocking; i++) {
                ASTNode expression=commonset.get(i);
                long weight=0L;
                if(isPlus) weight=commonsetweights.get(i);
                
                ASTNode pair1=expression;
                if(isPlus) pair1=new MultiplyMapper(expression, NumberConstant.make(weight));
                
                //System.out.println("pair1:"+pair1);
                
                // Iterate through expressions that tmp is in a pair with.
                Iterator<ASTNode> itpairs=pairs.get(pair1).iterator();
                while(itpairs.hasNext()  && !blocking) {
                    ASTNode pair2=itpairs.next();
                    
                    //System.out.println("pair2:"+pair2);
                    
                    // Check if pair2 is in commonset as well. If so, move on to the next pair2. 
                    if(isPlus) {
                        int csetidx=commonset.indexOf(pair2.getChild(0));
                        if(csetidx>-1 && commonsetweights.get(csetidx)==pair2.getChild(1).getValue() ) {
                            // If pair2 is in commonset, move on.
                            continue;
                        }
                    }
                    else {
                        // All other operators except +.
                        if(commonset.indexOf(pair2)>-1) {
                            continue;
                        }
                    }
                    
                    // Pair2 is outside commonset. Does it appear in a constraint that is not in ls?
                    
                    ASTNode tmp1=pair1;
                    ASTNode tmp2=pair2;
                    if(tmp1.hashCode()>tmp2.hashCode()) {
                        tmp2=pair1;  tmp1=pair2;
                    }
                    
                    PairASTNode pair12=new PairASTNode(tmp1, tmp2);
                    ArrayList<ASTNode> ls_other=exp.get(pair12);
                    
                    for(int j=0; j<ls_other.size(); j++) {
                        if(! ls.contains(ls_other.get(j))) {
                            blocking=true;
                            break;
                        }
                    }
                }
            }
            
            if(! blocking) {
                //System.out.println("Found non-blocking set:"+extentry.getValue());
                return extentry.getKey();
            }
            
        }
        
        // All entries in exp are blocking.
        //System.out.println("Did NOT find non-blocking set.");
        
        return null;
    }
    
    
    private boolean matches_type(ASTNode a) {
        if(type.equals("/\\") && a instanceof And) return true;
        if(type.equals("\\/") && a instanceof Or) return true;
        if(type.equals("+") && a instanceof WeightedSum) return true;
        if(type.equals("*") && a instanceof Times) return true;
        if(type.equals("xor") && a instanceof Xor) return true;
        return false;
    }
    
}


