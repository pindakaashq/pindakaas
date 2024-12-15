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

// To run before generic flattener. Preferably before any aux vars are introduced.
// Traverse expression tree and flatten identical expressions together, to the same aux variable.  

// Do longer expressions first

public class CSE 
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
            
            if(ls.size()==1) continue;
            
            // Remove items from ls that are no longer connected to the root because of other CSEs being flattened
            filterlist(ls);
            
            //System.out.println("After filtering, occurrences: "+ls.size());
            
            if(ls.size()>1) {
                // None of them are top-level relations. Do standard flattening.
                ASTNode auxvar=m.global_symbols.newAuxHelper(ls.get(0));
                
                for(ASTNode a : ls) {  // Replace all instances with the aux variable.
                    //int childno=a.getParent().getChildren().indexOf(a);
                    int childno=a.getChildNo();
                    a.getParent().setChild(childno, auxvar);   // copies auxvar and sets parent ptr of copy.
                }
                
                // Make the constraint that defines the aux variable. 
                // MUST NOT COPY ls.get(0) because it may contain other CSEs.
                assert ls.get(0).isDetached();
                
                ASTNode con;
                if(CmdFlags.use_polarity && CmdFlags.getSattrans() && (!CmdFlags.getSMTtrans()) && ls.get(0).isRelation()) {
                    int pol=ls.get(0).polarity();
                    for(ASTNode a : ls) {
                        if(a.polarity()!=pol) {
                            pol=0;
                        }
                    }
                    ls.get(0).setParent(null);    //  Do not copy.
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
                    ls.get(0).setParent(null);    //  Do not copy.
                    con=new ToVariable(ls.get(0), auxvar);  // No polarity reasoning
                }
                
                m.global_symbols.auxVarRepresentsConstraint( auxvar.toString(), "CSE: "+ls.size()+" occurrences of: "+(ls.get(0).toString()));
                
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
    
    //  In-place filter out detached expressions in an unordered list. 
    public static void filterlist(ArrayList<ASTNode> ls) {
        for(int i=0; i<ls.size(); i++) {
            if(ls.get(i).isDetached()) {
                ls.set(i, ls.get(ls.size()-1));
                ls.remove(ls.size()-1);
                i--;
            }
        }
    }
}


