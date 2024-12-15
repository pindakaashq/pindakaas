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
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import savilerow.expression.*;
import savilerow.model.Model;
import savilerow.treetransformer.TransformSimplify;

// Active AC-CSE on sums with the *-1 

public class ACCSEActiveSum
{
    private LinkedHashMap<PairASTNode, ArrayList<ASTNode>> exp;
    
    private HashMap<ASTNode, Long> expression_counts;    // If an expression only occurs once inside a sum, never add a pair containing that expression to exp.  
    
    private HashMap<PairASTNode, PairASTNode> pair_transform;
    
    public int numcse;
    public int countcse;
    public int totallength;
    
    public boolean active_ac_cs_found;
    
    public void flattenCSEs(Model m) {
        // Statistics
        numcse=0;     //  Number of CSE's
        countcse=0;   //  Total number of expressions replaced with auxvar.
        totallength=0;
        active_ac_cs_found=false;
        
        exp=new LinkedHashMap<PairASTNode, ArrayList<ASTNode>>();
        
        expression_counts=new HashMap<ASTNode, Long>();
        
        populate_expression_counts(m.constraints);   // Only does this once. Counts will go down as CSE's are eliminated but ignoring that. 
        
        populate_exp(m.constraints);
        
        // Cache the negated version of each pair. 
        pair_transform=new HashMap<PairASTNode, PairASTNode>();
        
        /*  Pre-fill pair_transform. 
        
        Iterator<Map.Entry<PairASTNode, ArrayList<ASTNode>>> it_populatetrans=exp.entrySet().iterator();
        
        while(it_populatetrans.hasNext()) {
            Map.Entry<PairASTNode, ArrayList<ASTNode>> object=it_populatetrans.next();
            
            PairASTNode key=object.getKey();
            PairASTNode pneg=new PairASTNode(key.e1.copy(), key.e2.copy());
            
            pneg.e1.setChild(1, NumberConstant.make(-pneg.e1.getChild(1).getValue()));  // negate the weight
            pneg.e2.setChild(1, NumberConstant.make(-pneg.e2.getChild(1).getValue()));  // negate the weight
            pair_transform.put(key, pneg);
        }*/
        
        ArrayList<ASTNode> new_constraints=new ArrayList<ASTNode>();
        
        while( ! exp.isEmpty() ) {
            PairASTNode key=heuristic();
            
            if(exp.isEmpty()) {
                // Bail out of the main loop.  
                break;
            }
            
            assert CmdFlags.accse_heuristic==1;
            
            ArrayList<ASTNode> ls=exp.get(key);    // heuristic 1. Largest list seen. 
            exp.remove(key);
            
            // Do the transform. 
            
            PairASTNode pneg=pair_transform.get(key);
            if(pneg==null) {
                pneg=new PairASTNode(key.e1.copy(), key.e2.copy());
                
                pneg.e1.setChild(1, NumberConstant.make(-pneg.e1.getChild(1).getValue()));  // negate the weight
                pneg.e2.setChild(1, NumberConstant.make(-pneg.e2.getChild(1).getValue()));  // negate the weight
                pair_transform.put(key, pneg);
            }
            
            ArrayList<ASTNode> ls_negated=exp.get(pneg);
            if(ls_negated==null) {
                ls_negated=new ArrayList<ASTNode>();
            }
            else {
                exp.remove(pneg);
                //System.out.println("Matched "+ls+" with negation "+ls_negated);
            }
            
            if(ls.size()+ls_negated.size() == 1) continue;   // Changed here for active. 
            
            // No need to remove duplicate entries in ls or ls_negated
            
            if(ls.size()>0 && ls_negated.size()>0) {
                active_ac_cs_found=true;
            }
            
            if(ls.size()+ls_negated.size() > 1) {
                // Find the largest set where /all/ elements are in each conjunction in ls.
                // Largest set gives most chance of cse var being set to true... in OR case. 
                ArrayList<ASTNode> commonset;
                ArrayList<Long> commonsetweights;
                
                Pair<ArrayList<ASTNode>, ArrayList<Long>> p1=buildCommonSetSums2(ls, ls_negated);
                commonset=p1.getFirst();
                commonsetweights=p1.getSecond();
                
                // Make the constraint for the positive set
                ASTNode con_inner=CommAssocFactory.makeCommAssoc("+", commonset, commonsetweights);
                
                ASTNode auxvar;
                if((!CmdFlags.getUsePropagateExtend()) || (ls_negated.size()==0)) {
                    //  Simple case -- no extended domain filtering, or no transforms. 
                    auxvar=m.global_symbols.newAuxHelper(con_inner);
                }
                else {
                    // Somewhat more complicated -- look up domain for the transform and do inverse transform on the domain, then intersect. 
                    ArrayList<Intpair> ls_bounds=con_inner.getIntervalSetExp();
                    ASTNode auxdom=m.filt.constructDomain(con_inner, Intpair.makeDomain(ls_bounds, con_inner.isRelation()));  //  Fetch filtered domain for con_inner
                    
                    TransformSimplify ts=new TransformSimplify();
                    ASTNode neg_con_inner=ts.transform(new UnaryMinus(con_inner.copy()));
                    Intpair neg_bounds=neg_con_inner.getBounds();
                    ASTNode neg_auxdom=m.filt.constructDomain(neg_con_inner, neg_bounds.lower, neg_bounds.upper);  //  Fetch filtered domain for neg_con_inner
                    
                    //  Use the negation component of CSEActive to negate the neg_auxdom.
                    CSETransform cset=new CSETransformMinus();
                    auxdom=new Intersect(auxdom, cset.inverse_transform_domain(neg_auxdom));
                    
                    auxdom=ts.transform(auxdom);
                    
                    auxvar=m.global_symbols.newAuxiliaryVariable(auxdom);
                    
                    m.filt.auxVarRepresentsAST(auxvar.toString(), con_inner);    // Associate one of the expressions with the aux variable.
                }
                
                ASTNode con=new ToVariable(con_inner, auxvar);
                
                for(ASTNode a : ls) {  // Replace all instances with the aux variable.
                    int childno=a.getChildNo();
                    
                    ArrayList<ASTNode> tmp=a.getChildren();
                    ArrayList<Long> tmpweights=((WeightedSum)a).getWeights();
                    
                    for(int i=0; i<commonset.size(); i++) {
                        int tmpidx=tmp.indexOf(commonset.get(i));
                        tmp.remove(tmpidx);
                        tmpweights.remove(tmpidx);
                    }
                    tmp.add(auxvar.copy());
                    tmpweights.add(1L);
                    
                    ASTNode replace_a=CommAssocFactory.makeCommAssoc("+", tmp, tmpweights);
                    
                    populate_exp(replace_a);
                    // Replaces the expression in ls with the new one.
                    a.getParent().setChild(childno, replace_a);
                    
                }
                
                // negate the weights
                for(int i=0; i<commonsetweights.size(); i++) {
                    commonsetweights.set(0, -commonsetweights.get(i));
                }
                
                for(ASTNode a : ls_negated) {  // Replace all instances with -aux
                    int childno=a.getChildNo();
                    
                    ArrayList<ASTNode> tmp=a.getChildren();
                    ArrayList<Long> tmpweights=((WeightedSum)a).getWeights();
                    
                    for(int i=0; i<commonset.size(); i++) {
                        int tmpidx=tmp.indexOf(commonset.get(i));
                        tmp.remove(tmpidx);
                        tmpweights.remove(tmpidx);
                    }
                    tmp.add(auxvar.copy());
                    tmpweights.add(-1L);
                    
                    ASTNode replace_a=CommAssocFactory.makeCommAssoc("+", tmp, tmpweights);
                    
                    populate_exp(replace_a);
                    // Replaces the expression in ls with the new one.
                    a.getParent().setChild(childno, replace_a);
                }
                
                m.global_symbols.auxVarRepresentsConstraint( auxvar.toString(), "CSE-ACCSE-SUM-Active: "+(ls.size()+ls_negated.size())+" occurrences of: "+(con_inner.toString()));
                
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
    
    private void populate_exp(ASTNode a)  {
        if( a instanceof WeightedSum) {
            
            ArrayList<ASTNode> children=a.getChildren();
            ArrayList<Long> wts=((WeightedSum)a).getWeights();
            
            ArrayList<ASTNode> mapped=new ArrayList<ASTNode>();
            for(int i=0; i<children.size(); i++) {
                ASTNode a1=new MultiplyMapper(children.get(i).copy(), NumberConstant.make(wts.get(i)));
                
                if( (!expression_counts.containsKey(children.get(i))) || expression_counts.get(children.get(i))>1L) {
                    mapped.add(a1);    /// Only add it if it occurs more than once globally, 
                    // or it is a new aux var (not in expression_counts, and guaranteed to occur more than once).
                }
                
                //mapped.add(a1);
            }
            
            for(int i=0; i<mapped.size(); i++) {
                for(int j=i+1; j<mapped.size(); j++) {
                    ASTNode a1=mapped.get(i);            
                    ASTNode a2=mapped.get(j);
                    
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
            populate_exp(a.getChild(i));
        }
    }
    
    
    private Pair<ArrayList<ASTNode>, ArrayList<Long>> buildCommonSetSums2(ArrayList<ASTNode> ls, ArrayList<ASTNode> ls_neg) {
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
        
        // do the negative ones.
        
        ah.clear();
        ahw.clear();
        for(ASTNode list : ls_neg) {
            ah.add(list.getChildren());
            ahw.add(((WeightedSum)list).getWeights());
        }
        
        for(int i=0; i<commonset.size(); i++) {
            ASTNode a=commonset.get(i);
            long w=commonsetweights.get(i);
            
            for(int j=0; j<ls_neg.size(); j++) {
                int a_index=ah.get(j).indexOf(a);
                if(a_index==-1  || ahw.get(j).get(a_index) != -w) {
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
    
    
    
    private PairASTNode heuristic() {
        Iterator<Map.Entry<PairASTNode, ArrayList<ASTNode>>> it=exp.entrySet().iterator();
        
        while(it.hasNext()) {
            Map.Entry<PairASTNode, ArrayList<ASTNode>> object=it.next();
            
            PairASTNode key=object.getKey();
            ArrayList<ASTNode> ls2=object.getValue();
            
            CSE.filterlist(ls2);      // updates list in place, in the hashtable.  
            
            if(ls2.size()==0) {
                it.remove();     // This pair has 0 occurrences, so get rid of it. 
            }
        }
        
        PairASTNode largestseen=null;
        int largestseen_size=-1;
        
        it=exp.entrySet().iterator();
        
        while(it.hasNext()) {
            Map.Entry<PairASTNode, ArrayList<ASTNode>> object=it.next();
            
            PairASTNode key=object.getKey();
            ArrayList<ASTNode> ls2=object.getValue();
            
            // Hacky version. Do the transform. 
            
            PairASTNode pneg=pair_transform.get(key);
            if(pneg==null) {
                pneg=new PairASTNode(key.e1.copy(), key.e2.copy());
                
                pneg.e1.setChild(1, NumberConstant.make(-pneg.e1.getChild(1).getValue()));  // negate the weight
                pneg.e2.setChild(1, NumberConstant.make(-pneg.e2.getChild(1).getValue()));  // negate the weight
                pair_transform.put(key, pneg);
            }
            
            ArrayList<ASTNode> ls_negated=exp.get(pneg);
            
            if(ls_negated==null) {
                
                if(ls2.size()<=1) {
                    // Only one occurrence of this pair,  and no negative version of this pair. 
                    it.remove();
                    continue;
                }
                
                if(ls2.size() > largestseen_size) {
                    largestseen=key;
                    largestseen_size=ls2.size();
                }
            }
            else {
                if(ls2.size()+ls_negated.size() >largestseen_size) {
                    largestseen=key;
                    largestseen_size=ls2.size()+ls_negated.size();
                }
            }
            
        }
        return largestseen;
    }
    
    private void populate_expression_counts(ASTNode a)  {
        if( a instanceof WeightedSum) {
            for(int i=0; i<a.numChildren(); i++) {
                ASTNode b=a.getChild(i);
                
                // Add the UN-WEIGHTED child expression in expression counts. Unweighted because we want to match positive and negative. 
                
                if(expression_counts.containsKey(b)) {
                    expression_counts.put(b, expression_counts.get(b)+1L);
                }
                else {
                    expression_counts.put(b, 1L);
                }
            }
        }
        
        for(int i=0; i<a.numChildren(); i++) {
            populate_expression_counts(a.getChild(i));
        }
    }
}


