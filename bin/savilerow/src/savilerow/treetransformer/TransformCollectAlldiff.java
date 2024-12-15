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

// Collect not-equal into Alldiff
// This one starts with edges and attempts to grow an alldiff from them.

// Other approach would be start with vars (expressions) and grow from each.
// But this might miss edges that could usefully be subsumed into alldiffs.

public class TransformCollectAlldiff extends TreeTransformerBottomUpNoWrapper
{
    public TransformCollectAlldiff(Model _m) { super(_m); }
    
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
                
                // Is it a binary not-equal or less.
                if( (cur instanceof AllDifferent 
                    && cur.getChild(0) instanceof CompoundMatrix
                    && cur.getChild(0).numChildren()==3)
                    || cur instanceof Less) {
                    
                    ASTNode var1ast;
                    ASTNode var2ast;
                    
                    if(cur instanceof AllDifferent) {
                        var1ast=cur.getChild(0).getChild(1);
                        var2ast=cur.getChild(0).getChild(2);
                    }
                    else {
                        var1ast=cur.getChild(0);
                        var2ast=cur.getChild(1);
                    }
                    
                    int var1=add_new_variable(var1ast, varslist, vartonum, adjlist);;
                    int var2=add_new_variable(var2ast, varslist, vartonum, adjlist);;
                    
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
                
                // Is it a non-binary alldiff
                if( cur instanceof AllDifferent 
                    && cur.getChild(0) instanceof CompoundMatrix
                    && cur.getChild(0).numChildren()>3) {
                    
                    ASTNode cm=cur.getChild(0);
                    ArrayList<Integer> vars_int=new ArrayList<Integer>();
                    
                    for(int j=1; j<cm.numChildren(); j++) {
                        vars_int.add(add_new_variable(cm.getChild(j), varslist, vartonum, adjlist));
                    }
                    
                    // Nothing inserted into cons. 
                    // Insert pairs into adjacency lists/sets in both directions.
                    for(int j=0; j<vars_int.size(); j++) {
                        for(int k=j+1; k<vars_int.size(); k++) {
                            adjlist.get(vars_int.get(j)).add(vars_int.get(k));
                            adjlist.get(vars_int.get(k)).add(vars_int.get(j));
                        }
                    }
                }
            }
            
            /*System.out.println(cons);
            System.out.println(varslist);
            System.out.println(vartonum);
            System.out.println("adjlist:");
            
            for(int i=0; i<adjlist.size(); i++) {
                
                System.out.println(varslist.get(i)+"="+convert_to_ast(new ArrayList<Integer>(adjlist.get(i)), varslist));
            }*/
            
            ArrayList<ASTNode> alldiffs=new ArrayList<ASTNode>();
            
            // Construct a new alldiff starting from a not-equal constraint
            // Start once from every not-equal, regardless of whether it has
            // already been subsumed by a new alldiff. 
            
            while(diseqs_left.size()>0) {
                Iterator<Pair<Integer,Integer>> it=diseqs_left.iterator();
                Pair<Integer,Integer> p1=it.next();
                
                ArrayList<Integer> newalldiff=new ArrayList<Integer>();
                
                newalldiff.add(p1.getFirst());
                newalldiff.add(p1.getSecond());
                
                //System.out.println("Starting with diseq: "+convert_to_ast(newalldiff, varslist));
                
                // Intersection to find vars that are adjacent to all entries in newalldiff.
                ArrayList<Integer> adjacent_to_all = new ArrayList<Integer>(adjlist.get(newalldiff.get(0)));
                
                intersect(adjacent_to_all, adjlist.get(newalldiff.get(1)));
                
                while(true) {
                    if(adjacent_to_all.size()==0) {
                        break;
                    }
                    else {
                        // arbitrarily take an element according to pseudorandom number
                        // COULD take element with highest degree
                        
                        newalldiff.add(adjacent_to_all.get(ran.nextInt(adjacent_to_all.size())));  
                        
                        // Update adjacent_to_all list
                        intersect(adjacent_to_all, adjlist.get(newalldiff.get(newalldiff.size()-1)));
                    }
                }
                
                for(int i=0; i<newalldiff.size(); i++) {
                    for(int j=0; j<newalldiff.size(); j++) {
                        if(i!=j) {
                            // Make the pair and remove from diseqs_left
                            Pair<Integer,Integer> prem=new Pair<Integer,Integer>(newalldiff.get(i), newalldiff.get(j));
                            diseqs_left.remove(prem);
                        }
                    }
                }
                
                if(newalldiff.size()>2) {
                    ArrayList<ASTNode> nalldiff=convert_to_ast(newalldiff, varslist);
                    
                    //System.out.println("Found a new alldiff:"+nalldiff);
                    
                    alldiffs.add(new AllDifferent(new CompoundMatrix(nalldiff)));
                    
                    // Throw away subsumed != constraints.
                    for(int j=0; j<newalldiff.size(); j++) {
                        for(int k=0; k<newalldiff.size(); k++) {
                            if(j!=k) {
                                Pair<Integer, Integer> p = new Pair<Integer, Integer>(newalldiff.get(j), newalldiff.get(k));
                                
                                // At this point we are definitely going to replace curnode, so can modify it in-place here. 
                                if(cons.containsKey(p)) {
                                    ArrayList<ASTNode> conslist=cons.get(p);
                                    for(int l=0; l<conslist.size(); l++) {
                                        if(conslist.get(l) instanceof AllDifferent && ! (conslist.get(l).isDetached())) {
                                            // If it's a binary not-equal, excise it. 
                                            int childno=conslist.get(l).getChildNo();
                                            conslist.get(l).getParent().setChild(childno, new BooleanConstant(true));
                                        }
                                    }
                                }
                                
                            }
                        }
                    }
                }
            }
            
            if(alldiffs.size()>0) {
                // Tag all the Ands. 
                return new NodeReplacement(new Tag(new And(new Tag(curnode), new Tag(new And(alldiffs)))));
            }
            
        }
        return null;
    }
    
    void intersect(ArrayList<Integer> adjacent_to_all, HashSet<Integer> curr_adjacent) {
        for(int k=0; k<adjacent_to_all.size(); k++) {
            if(! curr_adjacent.contains(adjacent_to_all.get(k))) {
                // If entry in adjacent_to_all is not in adjacency list of current element, remove it.
                adjacent_to_all.set(k, adjacent_to_all.get(adjacent_to_all.size()-1));
                adjacent_to_all.remove(adjacent_to_all.size()-1);
                k--;
                if(adjacent_to_all.size()==0) return;
            }
        }
    }
    
    ArrayList<ASTNode> convert_to_ast(ArrayList<Integer> ls, ArrayList<ASTNode> varslist) {
        ArrayList<ASTNode> nalldiff=new ArrayList<ASTNode>();
        for(int j=0; j<ls.size(); j++) {
            nalldiff.add(varslist.get(ls.get(j)));
        }
        return nalldiff;
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

