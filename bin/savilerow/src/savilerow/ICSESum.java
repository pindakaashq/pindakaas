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

import savilerow.expression.*;
import savilerow.model.*;
import savilerow.treetransformer.*;

// To run after standard 'identical' CSE.   Why is this necessary?

// Traverse expression tree and find common subsets between N-ary constraints.

// Identical Ands, Ors etc have already been eliminated by CSE.
// Also identical subexpressions have already been factored out of the ands, ors etc. 

public class ICSESum
{
    private HashMap<ASTNode, ArrayList<ASTNode>> inclusions;   // Links from nodes in AST to CS's. 
    
    private HashMap<ASTNode, ASTNode> commonsubex;   // All CS's seen so far. Avoid duplicates.  
    private HashMap<ASTNode, ASTNode> commonsubex_auxvar; // and the auxvar that the CS is equal to. 
    
    private ArrayList<ASTNode> list_sums;   // List of all sum expressions. 
    
    public int numcse;
    public int countcse;
    public int totallength;
    
    ///  If sums contain another operator that contains a sum, this CSE will almost certainly blow up horribly.  
    
    public void flattenCSEs(Model m) {
        ASTNode newcons=flattenCSEs(m.constraints, m.global_symbols, m);
        m.constraints=newcons;
    }
    
    public ASTNode flattenCSEs(ASTNode constraints, SymbolTable st, Model m) {
        // Statistics
        numcse=0;     //  Number of CSE's
        countcse=0;   //  Total number of expressions replaced with auxvar.
        totallength=0;
        
        ArrayList<ASTNode> new_constraints=new ArrayList<ASTNode>();
        ArrayList<ASTNode> new_aux_constraints=new ArrayList<ASTNode>();
        
        inclusions=new HashMap<ASTNode, ArrayList<ASTNode>>();
        
        commonsubex=new HashMap<ASTNode,ASTNode>();
        commonsubex_auxvar=new HashMap<ASTNode,ASTNode>();
        
        list_sums=new ArrayList<ASTNode>();
        
        HashMap<ASTNode, Integer> usecount=new HashMap<ASTNode, Integer>();  // maps commonsubex entries to the
        // number of times they have been used. Then in I-CSE-NC the ones that have been used 0 or 1 times
        // can be dealt with after the fact. 
        
        // Make a list of all sums in the model. 
        populate_list_sums(constraints);
        
        //  For each pair of sums, compute the intersection and (if it is not already there) add it to the list of new AC-CSs.
        for(int i=0; i<list_sums.size(); i++) {
            ASTNode sum1=list_sums.get(i);
            
            for(int j=i+1; j<list_sums.size(); j++) {
                ASTNode sum2=list_sums.get(j);
                
                Pair<ArrayList<ASTNode>, ArrayList<Long>> pcs=buildCommonSet(sum1, sum2);
                
                if(pcs.getFirst().size()>1) {
                    // There is a non-trivial AC-CS.
                    
                    // Make a sum. 
                    ASTNode cs=new WeightedSum(pcs.getFirst(), pcs.getSecond());
                    
                    // Sort. 
                    TransformNormalise tn=new TransformNormalise(m);
                    cs=tn.transform(cs);
                    
                    if(commonsubex.containsKey(cs)) {
                        cs=commonsubex.get(cs);   // get the unique one.
                        assert commonsubex_auxvar.containsKey(cs);
                    }
                    else {
                        commonsubex.put(cs, cs);
                        usecount.put(cs, 0);
                        // Create new aux var 
                        ASTNode auxvar=st.newAuxHelper(cs);
                        
                        ASTNode newconstraint=new ToVariable(cs, auxvar);
                        
                        commonsubex_auxvar.put(cs, auxvar);   // Store new aux var. 
                        new_aux_constraints.add(newconstraint);
                    }
                    
                    // Add the inclusion arcs. 
                    add_inclusion(sum1, cs);
                    add_inclusion(sum2, cs);
                    
                }
            }
        }
        
        for(int i=0; i<list_sums.size(); i++) {
            ASTNode sum1=list_sums.get(i);
            
            ArrayList<ASTNode> incl=new ArrayList<ASTNode>();
            
            if(inclusions.get(sum1)!=null) incl.addAll(inclusions.get(sum1));
            
            if(incl.size()>0) {
                
                int childno=sum1.getChildNo();
                ASTNode par=sum1.getParent();
                
                ArrayList<ASTNode> newsums=new ArrayList<ASTNode>();
                
                while(incl.size()>0) {
                    
                    ArrayList<ASTNode> newsum_children=sum1.getChildren();
                    ArrayList<Long> newsum_weights=((WeightedSum)sum1).getWeights();
                    
                    // Extract as many as possible of incl from newsum
                    
                    for(int k=0; k<incl.size(); k++) {
                        Pair<ArrayList<ASTNode>, ArrayList<Long>> p1=setDifference(newsum_children, newsum_weights, incl.get(k).getChildren(), ((WeightedSum)incl.get(k)).getWeights());
                        
                        if(p1!=null) {
                            
                            if(CmdFlags.accse_heuristic==21 && newsums.size()==0) {
                                // If this is the first sum (i.e. the one that will be used by -NC)
                                // then increment the counter. 
                                usecount.put(incl.get(k), usecount.get(incl.get(k))+1);
                            }
                            
                            
                            newsum_children=p1.getFirst();
                            newsum_weights=p1.getSecond();
                            
                            // Put in the auxvar. 
                            newsum_children.add(commonsubex_auxvar.get(incl.get(k)));
                            newsum_weights.add(1L);
                            
                            incl.remove(k);
                            k--;
                        }
                        
                    }
                    
                    ASTNode newsum=new WeightedSum(newsum_children, newsum_weights);
                    
                    newsums.add(newsum);
                }
                
                // Now have a list of sums to replace the original sum. Make the second pass to pack any further CS's into the sums. 
                
                incl.addAll(inclusions.get(sum1));  // start again with incl. 
                
                for(int s=0; s<newsums.size(); s++) {
                    
                    for(int k=0; k<incl.size(); k++) {
                        // try subtracting incl.get(k) from newsums.get(s)
                        // and see if it works. 
                        
                        Pair<ArrayList<ASTNode>, ArrayList<Long>> p1=setDifference(newsums.get(s).getChildren(), 
                            ((WeightedSum)newsums.get(s)).getWeights(), incl.get(k).getChildren(), ((WeightedSum)incl.get(k)).getWeights());
                        
                        if(p1!=null) {
                            // it worked.
                            
                            if(CmdFlags.accse_heuristic==21 && s==0) {
                                // If this is the first sum (i.e. the one that will be used by -NC)
                                // then increment the counter. 
                                usecount.put(incl.get(k), usecount.get(incl.get(k))+1);
                            }
                            
                            ArrayList<ASTNode> newsum_children=p1.getFirst();
                            ArrayList<Long> newsum_weights=p1.getSecond();
                            
                            // add the aux var
                            newsum_children.add(commonsubex_auxvar.get(incl.get(k)));
                            newsum_weights.add(1L);
                            
                            // Put the sum back. 
                            newsums.set(s, new WeightedSum(newsum_children, newsum_weights));
                        }
                    }
                    
                }
                
                // Now we have the final list of sums. Create a new aux var if there is more than one. 
                
                //System.out.println("newsums:");
                //System.out.println(newsums);
                
                if(newsums.size()>1) {
                    if(CmdFlags.accse_heuristic==20 || CmdFlags.accse_heuristic==30) {
                        ASTNode auxvar=st.newAuxHelper(newsums.get(0));
                        
                        for(int j=0; j<newsums.size(); j++) {
                            new_constraints.add(new ToVariable(newsums.get(j), auxvar));
                        }
                        
                        par.setChild(childno, auxvar);
                    }
                    else {
                        assert CmdFlags.accse_heuristic==21;
                        
                        // Just take one from the list and use that. I-CSE-NC 
                        par.setChild(childno, newsums.get(0));
                    }
                }
                else {
                    assert newsums.size()==1;
                    
                    // Replace old sum with newsums.get(0)
                    
                    par.setChild(childno, newsums.get(0));   // Should not copy. 
                }
                
                
            }
        }
        
        if(CmdFlags.accse_heuristic==21) {
            // Filter out the unused AC-CS aux vars. 
            // In this case all the new constraints define the AC-CS aux vars.
            
            for(ASTNode csx : usecount.keySet()) {
                int i=usecount.get(csx);
                if(i==0 || i==1) {
                    ASTNode newct=new ToVariable(csx, commonsubex_auxvar.get(csx));
                    
                    int loc=new_aux_constraints.indexOf(newct);
                    assert loc>=0;
                    
                    new_aux_constraints.set(loc, new_aux_constraints.get(new_aux_constraints.size()-1));
                    new_aux_constraints.remove(new_aux_constraints.size()-1);
                    
                    st.deleteSymbol(commonsubex_auxvar.get(csx).toString());
                    
                    //System.out.println("Deleted "+commonsubex_auxvar.get(csx));
                    //System.out.println(new_constraints);
                    
                }
                
                if(i==1) {
                    // Aux var is used once. Track down where it is used
                    // and sub the sum back in. 
                    
                    ReplaceASTNode r1=new ReplaceASTNode(commonsubex_auxvar.get(csx).copy(), csx.copy());
                    
                    // Since sum replacement was done in place, process the whole tree.
                    constraints=r1.transform(constraints);
                }
            }
        }
        
        // Conjoin all the new constraints onto the top level and return. 
        
        if(CmdFlags.accse_heuristic==30 && new_aux_constraints.size()>=2) {
            //  Make recursive call to continue CSE on the new constraints defining aux variables. 
            ICSESum recursive_obj=new ICSESum();
            ASTNode recursive_call=recursive_obj.flattenCSEs(new Top(new And(new_aux_constraints)), st, m);
            
            new_constraints.add(recursive_call.getChild(0));  // Add in constraints defining aux vars, and others made in the recursive call.
        }
        else {
            // Normal I-CSE(-NC) as described in Araya, Trombettoni etc paper. 
            new_constraints.addAll(new_aux_constraints);
        }
        new_constraints.add(constraints.getChild(0));
        constraints.setChild(0, new And(new_constraints));
        return constraints;
    }
    
    
    private void add_inclusion(ASTNode sum, ASTNode cs) {
        if(! inclusions.containsKey(sum)) {
            ArrayList<ASTNode> tmp=new ArrayList<ASTNode>();
            tmp.add(cs);
            inclusions.put(sum, tmp);
        }
        else {
            if(inclusions.get(sum).indexOf(cs)==-1) {  // don't add another inclusion if it's already there. 
                //  Can happen with three sums where two of the pairwise intersections are the same. 
                inclusions.get(sum).add(cs);
            }
        }
        
    }
    
    // Find all sums in the model. 
    // Bottom-up order. This is important for step 4 of Araya, Neveu and Trombettoni's algorithm. 
    private void populate_list_sums(ASTNode a) {
        for(int i=0; i<a.numChildren(); i++) {
            populate_list_sums(a.getChild(i));
        }
        
        if( a instanceof WeightedSum) {
            list_sums.add(a);
        }
    }
    
    private Pair<ArrayList<ASTNode>, ArrayList<Long>> buildCommonSet(ASTNode exp1, ASTNode exp2) {
        ArrayList<ASTNode> tmp=new ArrayList<ASTNode>();
        tmp.add(exp1);
        tmp.add(exp2);
        return buildCommonSet(tmp);
    }
    
    private Pair<ArrayList<ASTNode>, ArrayList<Long>> buildCommonSet(ArrayList<ASTNode> ls) {
        ArrayList<ArrayList<ASTNode>> ah=new ArrayList<ArrayList<ASTNode>>();
        for(ASTNode list : ls) {
            ah.add(list.getChildren());
        }
        
        ArrayList<ASTNode> commonset=ls.get(0).getChildren();
        ArrayList<Long> commonsetweights=((WeightedSum) ls.get(0)).getWeights();
        
        //System.out.println("-------------------------------");
        //System.out.println("Expressions:");
        //for(int i=0; i<ls.size(); i++) System.out.println(ls.get(i));
        //System.out.println("Common set (1):"+ commonset);
        //System.out.println("Common set weights (1):"+ commonsetweights);
        
        for(int i=0; i<commonset.size(); i++) {
            ASTNode a=commonset.get(i);
            long w=commonsetweights.get(i);
            
            for(int j=1; j<ls.size(); j++) {
                //int a_index=ah.get(j).indexOf(a);
                
                int a_index=-1;
                for(int k=0; k<ah.get(j).size(); k++) {
                    if(a.equals(ah.get(j).get(k))) {
                        a_index=k;
                        break;
                    }
                }
                
                if(a_index==-1  ||  ((WeightedSum)ls.get(j)).getWeight(a_index)!=w) {
                    // Either the child is not there or the weight does not match. 
                    commonset.set(i, commonset.get(commonset.size()-1));
                    commonset.remove(commonset.size()-1);
                    
                    commonsetweights.set(i, commonsetweights.get(commonsetweights.size()-1));
                    commonsetweights.remove(commonsetweights.size()-1);
                    
                    i--;   // do position i again. 
                    break;
                }
            }
        }
        //System.out.println("-------------------------------");
        //System.out.println("Expressions:");
        //for(int i=0; i<ls.size(); i++) System.out.println(ls.get(i));
        //System.out.println("Common set (2):"+ commonset);
        //System.out.println("Common set weights (2):"+ commonsetweights);
        
        return new Pair<ArrayList<ASTNode>, ArrayList<Long>>(commonset, commonsetweights);
    }
    
    private Pair<ArrayList<ASTNode>, ArrayList<Long>> setDifference(ArrayList<ASTNode> mainch, ArrayList<Long> mainw, ArrayList<ASTNode> subch, ArrayList<Long> subw) {
        ArrayList<ASTNode> outch=new ArrayList<ASTNode>();
        outch.addAll(mainch);
        ArrayList<Long> outw=new ArrayList<Long>();
        outw.addAll(mainw);
        
        for(int i=0; i<subch.size(); i++) {
            int idx=outch.indexOf(subch.get(i));
            if(idx==-1) return null;
            
            if(outw.get(idx)!=subw.get(i)) return null;
            
            outch.remove(idx);
            outw.remove(idx);
        }
        
        return new Pair<ArrayList<ASTNode>, ArrayList<Long>>(outch, outw);
    }
    
}


