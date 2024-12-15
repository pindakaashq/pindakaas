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
import java.util.Map;

import savilerow.expression.*;
import savilerow.model.Model;

// To run before generic flattener. Preferably before any aux vars are introduced.
// Traverse expression tree and flatten identical expressions together, to the same aux variable.  

// Do longer expressions first

public class CSETopLevel
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
        
        // Optimization pass before CSE: shove in any top-level defined values.
        Iterator<Map.Entry<ASTNode,ArrayList<ASTNode>>> iter = exp.entrySet().iterator();
        while (iter.hasNext()) {
            Map.Entry<ASTNode,ArrayList<ASTNode>> entry = iter.next();
            ArrayList<ASTNode> ls=entry.getValue();
            //System.out.println("Processing CSE: "+ls.size()+" occurrences of "+entry.getKey());
            
            if(ls.size()==1) {
                continue;
            }
            
            // Find out if any of them are top-level relations i.e. always true/false
            // COULD get rid of this if there was a rule to take top-level relation aux-vars and assign the var, propagate the consequences 
            // of assigning it through the model.
            boolean toplevel_defined=false;
            boolean toplevel_value=false;  // True or false, i.e. if an expression is found negated at the top level, the toplevel value is false.
            ASTNode toplevel_node=null;
            if(ls.get(0).isRelation()) {
                for(ASTNode a : ls) {
                    if(a.getParent()==null || 
                        (a.getParent().inTopConjunction())) {
                        toplevel_defined=true;
                        toplevel_value=true;
                        toplevel_node=a;
                        break;
                    }
                    if(a.getParent() instanceof Negate && a.getParent().getParent().inTopConjunction()) {
                        toplevel_defined=true;
                        toplevel_value=false;
                        toplevel_node=a;
                        break;
                    }
                }
            }
            
            if(toplevel_defined) {
                // Replace all non-top-level instances of this with toplevel_value
                for(ASTNode a : ls) {
                    if(a!=toplevel_node) {
                        //int childno=a.getParent().getChildren().indexOf(a);
                        int childno=a.getChildNo();
                        ASTNode replacement=new BooleanConstant(toplevel_value);
                        a.getParent().setChild(childno, replacement);
                        replacement.setParent(a.getParent()); // Should not need this line. 
                    }
                }
                
                numcse++;
                countcse+=ls.size();
                totallength+=ls.get(0).treesize();
            }
        }
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


