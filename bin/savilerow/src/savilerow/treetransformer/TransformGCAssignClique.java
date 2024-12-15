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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Random;

import savilerow.*;
import savilerow.expression.*;
import savilerow.model.Model;

// For graph colouring but could perhaps be generalised in some way.
// Find a large clique of != constraints and assign it the values 1..n
// to partially break value symmetry.  Must be done before variable symmetries are 
// detected and broken,  because it will remove some variable symmetries.

// Cut-n-pasted from TransformCollectAlldiff

public class TransformGCAssignClique extends TreeTransformerBottomUpNoWrapper
{
    public TransformGCAssignClique(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof And && !(curnode.getParent() instanceof Tag))
        {
            Random ran = CmdFlags.getRandomGen();  // deterministic greedy algorithm that uses pseudorandom numbers. 
            
            // Put pairs of not-equal expressions into hashtable.
            HashMap<Pair<Integer,Integer>, ArrayList<ASTNode>> cons=new HashMap<Pair<Integer,Integer>, ArrayList<ASTNode>>();
            
            ArrayList<ASTNode> varslist=new ArrayList<ASTNode>();  // Maps a number to an expression. Used to give a unique number to each variable/expression.
            HashMap<ASTNode, Integer> vartonum=new HashMap<ASTNode, Integer>();
            
            ArrayList<HashSet<Integer>> adjlist=new ArrayList<HashSet<Integer>>();
            
            LinkedHashSet<Pair<Integer, Integer>> diseqs_left=new LinkedHashSet<Pair<Integer, Integer>>();  /// Diseqs not yet included in a new alldiff constraint. 
            
            for(int i=0; i<curnode.numChildren(); i++) {
                ASTNode cur=curnode.getChild(i);
                
                // Is it a binary not-equal 
                if( cur instanceof AllDifferent 
                    && cur.getChild(0) instanceof CompoundMatrix
                    && cur.getChild(0).numChildren()==3) {
                    
                    ASTNode var1ast=cur.getChild(0).getChild(1);
                    ASTNode var2ast=cur.getChild(0).getChild(2);
                    
                    int var1=add_new_variable(var1ast, varslist, vartonum, adjlist);
                    int var2=add_new_variable(var2ast, varslist, vartonum, adjlist);
                    
                    // Insert into cons.  Only in one direction. 
                    Pair<Integer,Integer> p=new Pair<Integer,Integer>(var1, var2);
                    if(cons.containsKey(p)) {
                        cons.get(p).add(cur);
                    }
                    else {
                        ArrayList<ASTNode> tmp=new ArrayList<ASTNode>();
                        tmp.add(cur);
                        cons.put(p, tmp);
                    }
                    
                    // Insert into adjacency lists/sets in both directions. 
                    adjlist.get(var1).add(var2);
                    adjlist.get(var2).add(var1);
                    
                    // Insert into set of all diseqs
                    diseqs_left.add(p);
                }
            }
            
            ArrayList<Integer> largestClique=new ArrayList<Integer>();   // Largest clique found so far. 
            
            // Construct a new clique starting from a not-equal constraint
            // Start once from every not-equal, regardless of whether it has
            // already been subsumed by a new clique.
            
            Iterator<Pair<Integer,Integer>> it=diseqs_left.iterator();
            
            while(it.hasNext()) {
                Pair<Integer,Integer> p1=it.next();
                
                ArrayList<Integer> newclique=new ArrayList<Integer>();
                
                newclique.add(p1.getFirst());
                newclique.add(p1.getSecond());
                
                while(true) {
                    
                    // Intersection to find vars that are adjacent to all entries in newclique.
                    ArrayList<Integer> adjacent_to_all = new ArrayList<Integer>(adjlist.get(newclique.get(0)));
                    
                    intersection_loop:
                    for(int j=1; j<newclique.size(); j++) {
                        for(int k=0; k<adjacent_to_all.size(); k++) {
                            if(! adjlist.get(newclique.get(j)).contains(adjacent_to_all.get(k))) {
                                // If entry in adjacent_to_all is not in adjacency list of element j, remove it.
                                adjacent_to_all.set(k, adjacent_to_all.get(adjacent_to_all.size()-1));
                                adjacent_to_all.remove(adjacent_to_all.size()-1);
                                k--;
                                if(adjacent_to_all.size()==0) break intersection_loop;
                            }
                        }
                    }
                    
                    if(adjacent_to_all.size()==0) {
                        break;
                    }
                    else {
                        // arbitrarily take an element according to pseudorandom number
                        // COULD take element with highest degree here
                        
                        newclique.add(adjacent_to_all.get(ran.nextInt(adjacent_to_all.size())));  
                        //System.out.println("Extended clique:"+newclique);
                    }
                }
                
                if(newclique.size()>largestClique.size()) {
                    largestClique=newclique;
                }
            }
            
            // Make the new constraints
            
            ArrayList<ASTNode> newcons=new ArrayList<ASTNode>();
            
            for(int i=0; i<largestClique.size(); i++) {
                ASTNode var=varslist.get(largestClique.get(i));
                newcons.add(new Equals(var, NumberConstant.make(i+1)));
            }
            
            if(newcons.size()>0) {
                // Tag all the Ands. 
                return new NodeReplacement(new Tag(new And(new Tag(curnode), new Tag(new And(newcons)))));
            }
        }
        return null;
    }
    
    int add_new_variable(ASTNode varast, ArrayList<ASTNode> varslist, HashMap<ASTNode, Integer> vartonum, ArrayList<HashSet<Integer>> adjlist) {
        if(!vartonum.containsKey(varast)) {
            vartonum.put(varast, varslist.size());
            varslist.add(varast);
            adjlist.add(new HashSet<Integer>());  // Extend the adjacency list.
            assert adjlist.size()==varslist.size();
            return varslist.size()-1;
        }
        else {
            return vartonum.get(varast);
        }
    }
}

