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

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.TreeSet;

import gnu.trove.iterator.TIntIterator;
import gnu.trove.map.hash.TIntObjectHashMap;
import gnu.trove.set.hash.TIntHashSet;
import savilerow.expression.*;
import savilerow.model.*;

//  Store mutexes discovered by Minion between pairs of literals, and 
//  collect mutexes into AMO relations. 

public class AMODetect {
    ////////////////////////////////////////////////////////////////////////////
    //
    //   AMO adjacency list read from Minion during domain filtering.
    
    // Maps a number to a bool variable name. Used to give a unique number to each bool variable.
    // First entry should be null.
    public static ArrayList<String> varslist;
    public static HashMap<String, Integer> vartonum;  // Inverse mapping of above. 
    //  Adjlist maps from ints to ints.  Negative int means negated bool var. 
    public static TIntObjectHashMap<TIntHashSet> adjlist; 
    
    //   Only for strong AMO detection. 
    public static ArrayList<Pair<Pair<ASTNode, ASTNode>,Pair<Boolean, Boolean>>> mutexDetect=new ArrayList<>();
    
    public static void init() {
        //  Representation of adjacency list -- map between variables and integers
        varslist=new ArrayList<String>();  // Maps a number to a variable. Used to give a unique number to each variable.
        varslist.add(null);  // Can't use number 0. 
        
        vartonum=new HashMap<String, Integer>();
        //  Adjlist maps from ints to ints.
        adjlist=new TIntObjectHashMap<TIntHashSet>();
    }
    
    public static void addAMOSection(BufferedWriter b, Model m) throws IOException {
        assert CmdFlags.amo_detect_strong;
        // Scan constraints for AMOPB
        b.append("**MUTEXDETECT**\n");
        
        HashSet<Pair<Pair<ASTNode,ASTNode>,Pair<Boolean,Boolean>>> hs=new HashSet<>();
        
        b.append("[");
        ArrayList<ASTNode> ct=m.constraints.getChildren();
        
        while(ct.size()>0) {
            ASTNode curnode=ct.remove(ct.size()-1);
            if(curnode instanceof WeightedSum) {
                System.out.println("Dumping mutex pairs for: "+curnode.getParent());
                
                boolean sign=true;
                if(curnode.getParent() instanceof LessEqual && curnode.getChildNo()==1) {
                    sign=false;
                }
                
                for(int i=0; i<curnode.numChildren(); i++) {
                    if(curnode.getChild(i).isRelation()) {
                        for(int j=i+1; j<curnode.numChildren(); j++) {
                            if(curnode.getChild(j).isRelation()) {
                                ASTNode c1=curnode.getChild(i);
                                ASTNode c2=curnode.getChild(j);
                                
                                boolean signc1=sign ^ (c1 instanceof Negate) ^ ( ((WeightedSum)curnode).getWeight(i)<0 );
                                boolean signc2=sign ^ (c2 instanceof Negate) ^ ( ((WeightedSum)curnode).getWeight(j)<0 );
                                
                                Pair<ASTNode, ASTNode> p=new Pair<>((c1 instanceof Negate)?c1.getChild(0):c1, (c2 instanceof Negate)?c2.getChild(0):c2);
                                
                                Pair<Pair<ASTNode, ASTNode>, Pair<Boolean, Boolean>> pstore=new Pair<>(p, new Pair<Boolean, Boolean>(signc1, signc2));
                                
                                System.out.println(pstore);
                                
                                if(! hs.contains(pstore)) {
                                    hs.add(pstore);
                                    mutexDetect.add(pstore);   //  Add to the global list of potential mutexes to test
                                    
                                    if(c1 instanceof Negate) {
                                        b.append(c1.getChild(0).toString());
                                    }
                                    else {
                                        b.append(c1.toString());
                                    }
                                    b.append(signc1?",1,":",0,");
                                    
                                    if(c2 instanceof Negate) {
                                        b.append(c2.getChild(0).toString());
                                    }
                                    else {
                                        b.append(c2.toString());
                                    }
                                    b.append(signc2?",1,":",0,");
                                }
                            }
                        }
                    }
                }
            }
            else {
                ct.addAll(curnode.getChildren());
            }
        }
        b.append("]\n");
    }
    
    public static int add_variable_amo(String v) {
        v=v.intern();
        if(!vartonum.containsKey(v)) {
            int number=varslist.size();
            vartonum.put(v, number);
            varslist.add(v);
            adjlist.put(number, new TIntHashSet());    // Extend the adjacency list.
            adjlist.put(-number, new TIntHashSet());   
            return number;
        }
        else {
            return vartonum.get(v);
        }
    }
    
    public static void addEdge(int idx1, int idx2) {
        /*if(!hasEdge(idx1, idx2)) {
            //  Add in 1 direction only. 
            adjlist.get(idx1).add(idx2);
        }*/
        adjlist.get(idx1).add(idx2);
        adjlist.get(idx2).add(idx1);
    }
    
    public static boolean hasEdge(int idx1, int idx2) {
        return adjlist.get(idx1).contains(idx2);
    }
    
    public static void addEdge(int idx) {
        //  idx is index of the edge, with -X-AMO-extra
        Pair<Pair<ASTNode,ASTNode>, Pair<Boolean, Boolean>> p=mutexDetect.get(idx);
        
        ASTNode c1=p.getFirst().getFirst();
        ASTNode c2=p.getFirst().getSecond();
        
        boolean c1sign=p.getSecond().getFirst();
        boolean c2sign=p.getSecond().getFirst();
        
        //  Add the two variables
        int c1idx=add_variable_amo(c1.toString());
        int c2idx=add_variable_amo(c2.toString());
        
        addEdge(c1idx*(c1sign?1:-1), c2idx*(c2sign?1:-1));
    }
    
    //  Map from positive SAT literals to the internal numbers used in vartonum etc. 
    private static HashMap<Long, Integer> littonum;
    
    private static void buildLittonum(Sat satModel) {
        littonum=new HashMap<Long, Integer>();
        for(int i=1; i<varslist.size(); i++) {            
            long lit=satModel.getDirectVariable(varslist.get(i), 1);
            if(lit != -satModel.getTrue()) {
                littonum.put(lit, i);
            }
        }
    }
    
    //  Query if two SAT literals are mutex. 
    public static boolean isMutex(Sat satModel, long e1, long e2) {
        if(littonum==null) {
            buildLittonum(satModel);
        }
        
        long pose1=(e1<0)?(-e1):e1;
        long pose2=(e2<0)?(-e2):e2;
        
        if(!littonum.containsKey(pose1) || !littonum.containsKey(pose2)) {
            return false;
        }
        
        int nume1 = (e1<0)?(-littonum.get(pose1)):littonum.get(pose1);
        int nume2 = (e2<0)?(-littonum.get(pose2)):littonum.get(pose2);
        
        return hasEdge(nume1, nume2);
    }
    
    public static ArrayList<TreeSet<Integer>> buildCliques(TreeSet<String> loose_bools, HashMap<String, ASTNode> loose_coeffs) {
        for(String bool : loose_bools) {
            //  Make sure graph ds initialised for every variable in this ct. 
            AMODetect.add_variable_amo(bool);
        }
        
        //   Sort by degree within the sub-graph.
        //  Pair class used for sorting 
        class IdxDegreePair implements Comparable<IdxDegreePair> {
            public int idx;
            public int degree;
            public IdxDegreePair(int _idx, int _degree) {
                idx=_idx;
                degree=_degree;
            }
            public int compareTo(IdxDegreePair o) {
                if(degree<o.degree) {
                    return 1;
                }
                else if(degree==o.degree) {
                    return 0;
                }
                else {
                    return -1;
                }
            }
            public String toString() {
                return "("+idx+", "+degree+")";
            }
        }
        
        TIntHashSet loose_bools_idx_set=new TIntHashSet();  //  Set of available indices, opposite polarity ones get removed from here.
        
        ArrayList<IdxDegreePair> loose_bools_idx=new ArrayList<IdxDegreePair>(); //  List of all indices -- not just available ones.
        
        
        for(String varname : loose_bools) {
            int idx=vartonum.get(varname);
            
            loose_bools_idx_set.add(idx);
            loose_bools_idx_set.add(-idx);
        }
        
        // Populate loose_bools_idx then sort by degree.
        for(String varname : loose_bools) {
            int idx=vartonum.get(varname);
            // Degree of positive literal
            /*int degpos=0;
            TIntIterator adj_idx_iter=adjlist.get(idx).iterator();
            while(adj_idx_iter.hasNext()) {
                if(loose_bools_idx_set.contains(adj_idx_iter.next())) {
                    degpos++;
                }
            }*/
            int degpos=intersectionSize(adjlist.get(idx), loose_bools_idx_set);
            
            loose_bools_idx.add(new IdxDegreePair(idx, degpos));
            
            // Degree of negative literal
            /*int degneg=0;
            adj_idx_iter=adjlist.get(-idx).iterator();
            while(adj_idx_iter.hasNext()) {
                if(loose_bools_idx_set.contains(adj_idx_iter.next())) {
                    degneg++;
                }
            }*/
            int degneg=intersectionSize(adjlist.get(-idx), loose_bools_idx_set);
            
            loose_bools_idx.add(new IdxDegreePair(-idx, degneg));
        }
        
        Collections.sort(loose_bools_idx);
        
        //  Iterate through loose_bools_idx adding to cliques. 
        //  Makes a list of all connected vertices, then adds a max degree one that has most
        //  popular coeff in clique.
        ArrayList<TreeSet<Integer>> cliques=new ArrayList<TreeSet<Integer>>();
        
        long candidatesDegree=-1;
        ArrayList<Integer> candidates=new ArrayList<Integer>();
        
        for(int i=0; i<loose_bools_idx.size(); i++) {
            int v=loose_bools_idx.get(i).idx;
            
            if(loose_bools_idx_set.contains(v)) {
                //  Construct one clique.
                TreeSet<Integer> clique=new TreeSet<Integer>();
                
                loose_bools_idx_set.remove(v);
                loose_bools_idx_set.remove(-v);
                
                clique.add(v);
                
                while(true) {
                    
                    //  Make a list of max-degree candidates for inclusion in the clique.
                    candidatesDegree=-1;
                    candidates.clear();
                    
                    loose_bools_idx_loop:
                    for(int j=i+1; j<loose_bools_idx.size(); j++) {
                        int proposeVertex=loose_bools_idx.get(j).idx;
                        long proposeVertexDeg=loose_bools_idx.get(j).degree;
                        
                        if(candidatesDegree!=-1 && proposeVertexDeg<candidatesDegree) {
                            break loose_bools_idx_loop;  //  Gone past ones with same degree as other candidates.
                        }
                        
                        if(loose_bools_idx_set.contains(proposeVertex)) {
                            boolean connected=true;
                            
                            for(Integer cliqueVertex : clique) {
                                if(!hasEdge(cliqueVertex, proposeVertex)) {
                                    connected=false;
                                    break;
                                }
                            }
                            
                            if(connected) {
                                assert candidatesDegree==-1 || candidatesDegree==proposeVertexDeg;
                                candidatesDegree=proposeVertexDeg;
                                candidates.add(proposeVertex);
                            }
                        }
                    }
                    
                    if(candidates.size()==0) {
                        break;
                    }
                    
                    // Now we have all candidates of the highest possible degree.
                    // Choose one whose coeff is equal (absolute value) to the most others in the clique.
                    int proposeVertex=-1;
                    int coeffsCommon=-1;
                    
                    for(int j=0; j<candidates.size(); j++) {
                        int idx=candidates.get(j);
                        
                        String nam=varslist.get((idx<0)?-idx:idx);
                        long coeff=loose_coeffs.get(nam).getValue();
                        int coeffsCommonWithThis=0;
                        // Count how many from clique it is equal to.
                        for(int k : clique) {
                            String nam2=varslist.get((k<0)?-k:k);
                            if(loose_coeffs.get(nam2).getValue()==coeff) {
                                coeffsCommonWithThis++;
                            }
                        }
                        
                        if(coeffsCommonWithThis>coeffsCommon) {
                            coeffsCommon=coeffsCommonWithThis;
                            proposeVertex=idx;
                        }
                    }
                    
                    clique.add(proposeVertex);
                    loose_bools_idx_set.remove(proposeVertex);
                    loose_bools_idx_set.remove(-proposeVertex);
                }
                
                cliques.add(clique);
            }
        }
        
        return cliques;
    }
    
    static int intersectionSize(TIntHashSet a, TIntHashSet b) {
        int s=0;
        
        TIntHashSet iterset=a;
        TIntHashSet otherset=b;
        if(b.size()<a.size()) {
            iterset=b;
            otherset=a;
        }
        
        TIntIterator adj_idx_iter=iterset.iterator();
        while(adj_idx_iter.hasNext()) {
            if(otherset.contains(adj_idx_iter.next())) {
                s++;
            }
        }
        
        return s;
    }
}