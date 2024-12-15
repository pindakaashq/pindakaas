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








import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import savilerow.expression.*;
import savilerow.model.Model;

// Active AC-CSE on sums with the *-1 

public class ACCSEActiveSum2
{
    // Map from pairs of expressions p ( e.g. 2x, 3y) to a list of pairs: m, expression where m*p is in expression. 
    private LinkedHashMap<PairASTNode, ArrayList<Pair<Long, ASTNode>>> exp;
    // First coeff of pair is always positive.
    
    private HashMap<ASTNode, Long> expression_counts;    // If an expression only occurs once inside a sum, never add a pair containing that expression to exp.  
    
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
        
        exp=new LinkedHashMap<PairASTNode, ArrayList<Pair<Long,ASTNode>>>();
        
        expression_counts=new HashMap<ASTNode, Long>();
        
        assert CmdFlags.accse_heuristic==1;   // heuristic 1. Most occurrences of AC-CS first. 
        
        populate_expression_counts(m.constraints);   // Only does this once. Counts will go down as CSE's are eliminated but ignoring that. 
        
        populate_exp(m.constraints);
        ArrayList<ASTNode> new_constraints=new ArrayList<ASTNode>();
        
        while( ! exp.isEmpty() ) {
            PairASTNode key=heuristic();
            
            if(exp.isEmpty()) {
                // Bail out of the main loop.  
                break;
            }
            
            ArrayList<Pair<Long,ASTNode>> ls=exp.get(key); 
            exp.remove(key);
            
            if(ls.size()<2) {
                continue;
            }
            
            ArrayList<ASTNode> cset=new ArrayList<ASTNode>();
            cset.add(key.e1.getChild(0));
            cset.add(key.e2.getChild(0));
            ArrayList<Long> csetwts=new ArrayList<Long>();
            csetwts.add(key.e1.getChild(1).getValue());
            csetwts.add(key.e2.getChild(1).getValue());
            
            growCommonSet(cset, csetwts, ls);   ///  Add any other terms that are also in all elements of ls, in the same proportion.
            
            ASTNode con_inner=CommAssocFactory.makeCommAssoc("+", cset, csetwts);
            
            ASTNode auxvar=m.global_symbols.newAuxHelper(con_inner);    //  NOT FINISHED HERE --- does not work properly with extended dom filt. Assumes no transforms.
            
            ASTNode con=new ToVariable(con_inner, auxvar);
            
            System.out.println("AC-CS: "+con_inner);
            
            for(Pair<Long,ASTNode> a : ls) {  // Replace all instances with the aux variable.
                int childno=a.getSecond().getChildNo();
                
                ArrayList<ASTNode> tmp=a.getSecond().getChildren();
                ArrayList<Long> tmpweights=((WeightedSum)a.getSecond()).getWeights();
                
                long factor=a.getFirst();  // multiple of the aux var. 
                
                if(factor!=1L) {
                    active_ac_cs_found=true;
                }
                
                for(int i=0; i<cset.size(); i++) {
                    int tmpidx1=tmp.indexOf(cset.get(i));
                    tmp.set(tmpidx1, tmp.get(tmp.size()-1));
                    tmp.remove(tmp.size()-1);
                    tmpweights.set(tmpidx1, tmpweights.get(tmpweights.size()-1));
                    tmpweights.remove(tmpweights.size()-1);
                }
                
                tmp.add(auxvar.copy());
                tmpweights.add(factor);
                
                ASTNode replace_a=CommAssocFactory.makeCommAssoc("+", tmp, tmpweights);
                
                populate_exp(replace_a);
                // Replaces the expression in ls with the new one.
                System.out.println("  Replacing "+a+"   with   "+replace_a);                 
                a.getSecond().getParent().setChild(childno, replace_a);
            }
            
            if(numcse>1 && false) {
                break;
            }
            
            populate_exp(con);
            
            m.global_symbols.auxVarRepresentsConstraint( auxvar.toString(), "CSE-ACCSE-SUM-Active2: "+(ls.size())+" occurrences of: "+(con_inner.toString()));
            
            new_constraints.add(con);
            
            numcse++;
            countcse+=ls.size();
            totallength+=cset.size()*ls.size();
        }
        
        // Conjoin all the new constraints onto the top level.
        m.constraints.getChild(0).setParent(null);
        new_constraints.add(m.constraints.getChild(0));
        m.constraints.setChild(0, new And(new_constraints));
    }
    
    
    private void growCommonSet(ArrayList<ASTNode> cset, ArrayList<Long> csetwts, ArrayList<Pair<Long,ASTNode>> ls) {
        return;   // minimal correct impl.
    }
    
    /*
    private void growCommonSet(ArrayList<ASTNode> cset, ArrayList<Long> csetwts, ArrayList<Pair<Long,ASTNode>> ls) {
        // Does not find the global maximum sized common set, just a maximal one (i.e. no single element can be added).
        
        ASTNode a=cset.get(0);
        long awt=csetwts.get(0);
        
        ASTNode b=cset.get(1);
        long bwt=csetwts.get(1);
        
        // Find shortest sum in ls first.
        int idx_shortest=0;
        for(int i=1; i<ls.size(); i++) {
            if(ls.get(idx_shortest).getSecond().numChildren()>ls.get(i).getSecond().numChildren()) {
                idx_shortest=i;
            }
        }
        
        // Factor from cset to ls[idx_shortest]   i.e. coeff of the aux var.
        long factor=ls.get(idx_shortest).getFirst();
        
        // Unpack the shortest sum
        ArrayList<ASTNode> shortsum=ls.get(idx_shortest).getSecond().getChildren();
        ArrayList<Long> shortsumwts=((WeightedSum)ls.get(idx_shortest).getSecond()).getWeights();
        
        // For each element in shortsum, first check if it has an integer coeff when divided by factor.
        // a and b must have integer coeff.
        for(int i=shortsum.size()-1; i>=0; i--) {
            if( (shortsumwts.get(i)%factor) != 0) {
                // This item can't be added to the AC-CS because it would not have an integer coefficient in the ct defining the aux var. 
                shortsum.set(i, shortsum.get(shortsum.size()-1));
                shortsum.remove(shortsum.size()-1);
                shortsumwts.set(i, shortsumwts.get(shortsumwts.size()-1));
                shortsumwts.remove(shortsumwts.size()-1);
            }
            else {
                shortsumwts.set(i, shortsumwts.get(i)/factor);  // Convert to AC-CS multiple.
            }
        }
        
        assert shortsumwts.get(shortsum.indexOf(a))==awt;
        assert shortsumwts.get(shortsum.indexOf(b))==bwt;
        
        // Iterate through other sums in ls, getting rid of any terms that do not appear (or not in same proportion)
        
        iloop:
        for(int i=shortsum.size()-1; i>=0; i--) {
            ASTNode c=shortsum.get(i);
            long cwt=shortsumwts.get(i);
            
            if(!(c.equals(a)) && !(c.equals(b))) {  // Don't take out either a or b.   We know they are in the same proportion everywhere.
                
                // Go through ls (except idx_shortest) checking c is in same proportion to a everywhere.
                double factor_a_c=((double)awt)/((double)cwt);
                
                for(int j=0; j<ls.size(); j++) {
                    if(j!=idx_shortest) {
                        ASTNode jsum=ls.get(j).getSecond();
                        ArrayList<ASTNode> jsumch=jsum.getChildren();
                        
                        int c_idx_lsj=jsumch.indexOf(c);
                        if(c_idx_lsj==-1) {
                            // c not contained in jsum.  Remove from common set
                            shortsum.remove(i);
                            shortsumwts.remove(i);
                            continue iloop;
                        }
                        else {
                            int a_idx_lsj=jsumch.indexOf(a);
                            
                            if( ((double) ( ((WeightedSum)jsum).getWeight(a_idx_lsj)))/( (double) (((WeightedSum)jsum).getWeight(c_idx_lsj))) != factor_a_c ) {
                                shortsum.remove(i);
                                shortsumwts.remove(i);
                                continue iloop;
                            }
                        }
                    }
                }
                
                
            }
        }
        
        if(shortsum.size()>2) {
            // replace cset with shortsum
            cset.clear();
            csetwts.clear();
            cset.addAll(shortsum);
            csetwts.addAll(shortsumwts);
        }
        
        return;
    }*/
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //  Populate map from pairs to list of expressions containing the pair. 
    //  This one ignores the coeffs.
    
    private void populate_exp(ASTNode a)  {
        if( a instanceof WeightedSum) {
            for(int i=0; i<a.numChildren(); i++) {
                ASTNode a1=a.getChild(i);
                
                if( (!expression_counts.containsKey(a1)) || expression_counts.get(a1)>1L) {
                    /// Only continue if it occurs more than once globally, 
                    // or it is a new aux var (not in expression_counts, and guaranteed to occur more than once when it is introduced).
                    for(int j=i+1; j<a.numChildren(); j++) {
                        ASTNode a2=a.getChild(j);
                        if( (!expression_counts.containsKey(a2)) || expression_counts.get(a2)>1L) {
                            
                            // Factor out the GCD of the pair
                            long wa1=((WeightedSum)a).getWeight(i);
                            long wa2=((WeightedSum)a).getWeight(j);
                            BigInteger gcd=BigInteger.valueOf(wa1).gcd(BigInteger.valueOf(wa2));
                            long lgcd=gcd.longValue();
                            
                            // Order the two expressions
                            if(a1.hashCode() > a2.hashCode()) {
                                ASTNode tmp=a2;
                                a2=a1;
                                a1=tmp;
                                long tmp2=wa2;
                                wa2=wa1;
                                wa1=tmp2;
                            }
                            
                            // Make first var positive.
                            if(wa1/lgcd < 0) {
                                lgcd=-lgcd;
                            }
                            
                            ASTNode a1m=new MultiplyMapper(a1,NumberConstant.make(wa1/lgcd));
                            ASTNode a2m=new MultiplyMapper(a2,NumberConstant.make(wa2/lgcd));
                            
                            PairASTNode p=new PairASTNode(a1m, a2m);
                            
                            System.out.println("Adding mapping: "+p+" ---->  "+a);
                            
                            if(exp.containsKey(p)) {
                                exp.get(p).add(new Pair<Long, ASTNode>(lgcd, a));
                            }
                            else {
                                ArrayList<Pair<Long, ASTNode>> list=new ArrayList<Pair<Long, ASTNode>>();
                                list.add(new Pair<Long, ASTNode>(lgcd, a));
                                exp.put(p, list);
                            }
                        }
                    }
                }
            }
        }
        
        for(int i=0; i<a.numChildren(); i++) {
            populate_exp(a.getChild(i));
        }
    }
    
    //  In-place filter out detached expressions in an unordered list. 
    public void filterlist(ArrayList<Pair<Long,ASTNode>> ls) {
        for(int i=ls.size()-1; i>=0; i--) {
            if(ls.get(i).getSecond().isDetached()) {
                ls.set(i, ls.get(ls.size()-1));
                ls.remove(ls.size()-1);
            }
        }
    }
    
    private PairASTNode heuristic() {
        Iterator<Map.Entry<PairASTNode, ArrayList<Pair<Long,ASTNode>>>> it=exp.entrySet().iterator();
        
        while(it.hasNext()) {
            Map.Entry<PairASTNode, ArrayList<Pair<Long,ASTNode>>> object=it.next();
            
            PairASTNode key=object.getKey();
            ArrayList<Pair<Long,ASTNode>> ls2=object.getValue();
            
            filterlist(ls2);      // updates list in place, in the hashtable.  
            
            if(ls2.size()<2) {
                it.remove();     // This pair has 0 or 1 occurrences, so get rid of it. 
            }
        }
        
        PairASTNode largestseen=null;
        int largestseen_size=-1;
        
        it=exp.entrySet().iterator();
        
        while(it.hasNext()) {
            Map.Entry<PairASTNode, ArrayList<Pair<Long,ASTNode>>> object=it.next();
            
            PairASTNode key=object.getKey();
            ArrayList<Pair<Long,ASTNode>> ls2=object.getValue();
            
            if(ls2.size()>largestseen_size) {
                largestseen=key;
                largestseen_size=ls2.size();
            }
        }
        return largestseen;
    }
    
    
    private void populate_expression_counts(ASTNode a)  {
        if( a instanceof WeightedSum) {
            for(int i=0; i<a.numChildren(); i++) {
                ASTNode b=a.getChild(i);
                
                // Add the UN-WEIGHTED child expression in expression counts.
                
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


