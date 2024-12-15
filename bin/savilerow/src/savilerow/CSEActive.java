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
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;

import savilerow.expression.*;
import savilerow.model.Model;
import savilerow.treetransformer.*;

// To run before generic flattener. Preferably before any aux vars are introduced.
// Traverse expression tree and flatten identical expressions together, to the same aux variable.  

// Do longer expressions first

public class CSEActive 
{
    private HashMap<ASTNode, ArrayList<ASTNode>> exp;
    
    public int numcse;
    public int countcse;
    public int totallength;
    
    public void flattenCSEs(Model m) {
        // Statistics
        numcse=0;     //  Number of CSE's
        countcse=0;   //  Total number of expressions replaced with auxvar.
        totallength=0;
        
        exp=new HashMap<ASTNode, ArrayList<ASTNode>>();
        // Map from a string representation of an expression to a set of pointers to where it occurs in the tree.
        
        populate_exp(m.constraints);
        
        // Equivalence classes. 
        // Set up an ArrayList of transforms.
        ArrayList<CSETransform> transforms=new ArrayList<CSETransform>();
        
        // CSETransforms
        transforms.add(new CSETransformNeg());
        transforms.add(new CSETransformMinus());
        transforms.add(new CSETransformTimes(2));
        transforms.add(new CSETransformTimes(-2));
        
        //System.out.println("In CSE, exp:"+exp);
        // Dump exp into an arraylist
        ArrayList<Map.Entry<ASTNode, ArrayList<ASTNode>>> exp2=new ArrayList<Map.Entry<ASTNode, ArrayList<ASTNode>>>(exp.entrySet());
        
        // Sort for largest expression first.
        class cmpstrings implements Comparator<Map.Entry<ASTNode, ArrayList<ASTNode>>> {
            public int compare(Map.Entry<ASTNode, ArrayList<ASTNode>> x, Map.Entry<ASTNode, ArrayList<ASTNode>> y) {
                int sizex=x.getKey().treesize();
                int sizey=y.getKey().treesize();
                if(sizex>sizey) return -1;   // x<y
                if(sizex==sizey) {  // // x==y
                    // To get a consistent ordering, now compare hashcodes.
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
                return 1;  // x>y
            }
        }
        cmpstrings cmpstrings1=new cmpstrings();
        Collections.sort(exp2, cmpstrings1);
        ArrayList<ASTNode> new_constraints=new ArrayList<ASTNode>();
        
        
        for(Map.Entry<ASTNode,ArrayList<ASTNode>> entry : exp2) {
            
            
            ArrayList<ASTNode> ls=entry.getValue();
            //System.out.println("Processing CSE: "+ls.size()+" occurrences of "+entry.getKey());
            
            // Remove items from ls that are no longer connected to the root because of other CSEs being flattened
            CSE.filterlist(ls);
            
            if(ls.size()==0) continue;
            
            TransformSimplify ts=new TransformSimplify();
            TransformNormalise tn=new TransformNormalise(m);
            
            // Do any of the transforms give a match?
            boolean transforms_exist=false;
            
            for(int i=0; i<transforms.size(); i++) {
                if(transforms.get(i).applicable(entry.getKey())) {
                    ASTNode trans=transforms.get(i).transform(entry.getKey().copy());
                    
                    trans=ts.transform(trans);  // simplify
                    trans=tn.transform(trans);  // normalise.
                    
                    ArrayList<ASTNode> trans_ls=exp.get(trans);
                    
                    // Must not match an expression (e.g. !A) to something contained in it (e.g. A, using negation transform)
                    // Or vice versa, matching an expression (e.g. A) to something that contains it (e.g. !A).
                    
                    if(trans_ls!=null && !entry.getKey().contains(trans) && !trans.contains(entry.getKey()) ) {
                        // need to check there is something in there that is not detached
                        // Filter the list. 
                        CSE.filterlist(trans_ls);
                        
                        if(trans_ls.size()>0) {
                            transforms_exist=true;
                            // Don't break here so all the relevant lists are filtered. 
                        }
                    }
                }
            }
            
            if(ls.size()>1 || transforms_exist) {
                
                //  Create an auxiliary variable for ls and its transforms.
                ASTNode auxvar;
                if((!CmdFlags.getUsePropagateExtend()) || (!transforms_exist)) {
                    //  Simple case -- no extended domain filtering, or no transforms. 
                    auxvar=m.global_symbols.newAuxHelper(ls.get(0));
                }
                else {
                    // Complicated -- look up domain for each transform and do the inverse transform on the domain, then intersect them all. 
                    
                    ArrayList<Intpair> ls_bounds=ls.get(0).getIntervalSetExp();
                    ASTNode auxdom=m.filt.constructDomain(ls.get(0), Intpair.makeDomain(ls_bounds, ls.get(0).isRelation()));  //  Fetch filtered domain for ls.get(0)
                    boolean isBool=auxdom.isBooleanSet();
                    
                    for(int i=0; i<transforms.size(); i++) {
                        if(transforms.get(i).applicable(entry.getKey())) {
                            ASTNode trans=transforms.get(i).transform(entry.getKey().copy());
                            
                            trans=ts.transform(trans); // simplify
                            trans=tn.transform(trans); // normalise
                            ArrayList<ASTNode> ls2=exp.get(trans);
                            if(ls2!=null && !entry.getKey().contains(trans) && !trans.contains(entry.getKey())) {
                                if(ls2.size()>0) {
                                    ArrayList<Intpair> trans_bounds=trans.getIntervalSetExp();
                                    ASTNode trans_auxdom=m.filt.constructDomain(trans, Intpair.makeDomain(trans_bounds, trans.isRelation()));
                                    ArrayList<Intpair> trans_auxdom_intervals=trans_auxdom.getIntervalSet();
                                    if(! trans_auxdom_intervals.equals(trans_bounds)) {
                                        //  Now we have the filtered domain for the transformed expression (e.g. 2 x e). Do the inverse transformation
                                        //  on the domain. 
                                        ASTNode inv_trans_auxdom=transforms.get(i).inverse_transform_domain(trans_auxdom);
                                        isBool = isBool || inv_trans_auxdom.isBooleanSet();
                                        auxdom=new Intersect(auxdom, inv_trans_auxdom);
                                    }
                                }
                            }
                        }
                    }
                    
                    auxdom=ts.transform(auxdom);
                    
                    if(isBool) {
                        auxdom=Intpair.makeDomain(auxdom.getIntervalSet(), true);  // Make it a boolean set.
                    }
                    
                    auxvar=m.global_symbols.newAuxiliaryVariable(auxdom);
                    
                    m.filt.auxVarRepresentsAST(auxvar.toString(), ls.get(0));    // Associate one of the expressions with the aux variable.
                }
                
                int numoccs=0;
                
                for(ASTNode a : ls) {  // Replace all instances with the aux variable.
                    CmdFlags.printlnIfVerbose("Replacing "+a+" with "+auxvar);
                    int childno=a.getChildNo();
                    a.getParent().setChild(childno, auxvar);   // copies auxvar
                    numoccs++;
                }
                
                if(transforms_exist) {
                    for(int i=0; i<transforms.size(); i++) {
                        if(transforms.get(i).applicable(entry.getKey())) {
                            ASTNode trans=transforms.get(i).transform(entry.getKey().copy());
                            
                            ASTNode aux_ref=transforms.get(i).transform(auxvar.copy());
                            
                            trans=ts.transform(trans); // simplify
                            trans=tn.transform(trans); // normalise
                            
                            // These probably do nothing, but applying them just in case. 
                            aux_ref=ts.transform(aux_ref);  // simplify
                            aux_ref=tn.transform(aux_ref);  // normalise
                            
                            ArrayList<ASTNode> ls2=exp.get(trans);
                            if(ls2!=null && !entry.getKey().contains(trans) && !trans.contains(entry.getKey())) {
                                if(ls2.size()>0) {
                                    for(ASTNode a : ls2) {
                                        //  cannot be detached, list already filtered. 
                                        CmdFlags.printlnIfVerbose("Replacing "+a+" with "+aux_ref);
                                        int childno=a.getChildNo();
                                        a.getParent().setChild(childno, aux_ref);   // copies aux_ref
                                        numoccs++;
                                    }
                                }
                            }
                        }
                    }
                }
                
                // Make the constraint that defines the aux variable. 
                ASTNode con;
                if(CmdFlags.use_polarity && CmdFlags.getSattrans() && (!CmdFlags.getSMTtrans()) && ls.get(0).isRelation()) {
                    int pol=ls.get(0).polarity();
                    for(ASTNode a : ls) {
                        if(a.polarity()!=pol) {
                            pol=0;
                            break;
                        }
                    }
                    if(transforms_exist && pol!=0) {
                        for(int i=0; i<transforms.size(); i++) {
                            int sign=1;  // Whether to flip the sign of the polarity of the expression. 
                            
                            if(transforms.get(i) instanceof CSETransformNeg || transforms.get(i) instanceof CSETransformMinus 
                                || (transforms.get(i) instanceof CSETransformTimes && ((CSETransformTimes) (transforms.get(i))).num<0)) {
                                sign=-1;
                            }
                            
                            ASTNode trans=transforms.get(i).transform(entry.getKey().copy());
                            trans=ts.transform(trans); // simplify
                            trans=tn.transform(trans); // normalise
                            
                            ArrayList<ASTNode> ls2=exp.get(trans);
                            if(ls2!=null && !entry.getKey().contains(trans) && !trans.contains(entry.getKey())) {
                                for(ASTNode a : ls2) {
                                    if( (sign*a.polarity()) != pol ) {
                                        pol=0;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    
                    if(pol==1) {
                        con=new Implies(auxvar, ls.get(0));
                    }
                    else if (pol==-1 && ls.get(0).isNegatable()) {
                        //  If the polarity is negative and the constraint has a compact negation available, then generate the negative implication. 
                        con=new Implies(new Negate(auxvar), new Negate(ls.get(0)));
                    }
                    else {
                        con=new ToVariable(ls.get(0), auxvar);
                    }
                }
                else {
                    con=new ToVariable(ls.get(0), auxvar);  // No polarity reasoning
                }
                
                populate_exp(con);
                
                m.global_symbols.auxVarRepresentsConstraint( auxvar.toString(), "Active-CSE: "+numoccs+" occurrences of this expression or equivalent: "+(ls.get(0).toString()));
                
                new_constraints.add(con);
                
                numcse++;
                countcse+=numoccs;
                totallength+=entry.getKey().treesize();
            }
        }
        
        // Conjoin all the new constraints onto the top level.
        m.constraints.getChild(0).setParent(null);
        new_constraints.add(m.constraints.getChild(0));
        m.constraints.setChild(0, new And(new_constraints));
    }
    
    private void populate_exp(ASTNode a)  {
        // If a is a potential CSE...
        if(a.toCSE()) {
            if(exp.containsKey(a)) {
                exp.get(a).add(a);
            }
            else {
                ArrayList<ASTNode> list=new ArrayList<ASTNode>();
                list.add(a);
                exp.put(a, list);
            }
        }
        
        for(int i=0; i<a.numChildren(); i++) {
            populate_exp(a.getChild(i));
        }
    }
}


