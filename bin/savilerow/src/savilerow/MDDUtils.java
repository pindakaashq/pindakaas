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

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;

import savilerow.expression.*;
import savilerow.model.Sat;

public class MDDUtils {
    public static class MDDNode {
        MDDNode parent;
        ArrayList<Long> values;
        ArrayList<MDDNode> links;
        
        int id;   // Integer that uniquely defines this node. 
        byte type;  // 0 normal, -1 for tt, -2 for ff. 
        
        MDDNode(MDDNode _parent) {
            parent=_parent;
            type=0;
            values=new ArrayList<>();
            links=new ArrayList<>();
        }
    }
    
    // Construct an MDD from a set of tuples in lex order. 
    // Returns the top node of the MDD. 
    public static void MDDEncode(ArrayList<ASTNode> vars, ArrayList<ASTNode> tuples, Sat satModel) throws IOException {
        Pair<MDDNode, ArrayList<MDDNode>> p=constructMDD(tuples);
        
        encodeMDDSAT(satModel, vars, p.getFirst(), p.getSecond());
    }
    
    
    public static Pair<MDDNode, ArrayList<MDDNode>> constructMDD(ArrayList<ASTNode> tuples) {
        ArrayList<MDDNode> mddnodes=new ArrayList<>();
        // Make the top node. 
        MDDNode top=new MDDNode(null);
        
        mddnodes.add(top);
        
        int tuplelen=tuples.get(0).getTupleLength();
        
        // Reuse tuple
        long[] tup=new long[tuplelen];
        
        for(int tupid=0; tupid<tuples.size(); tupid++) {
            for(int i=0; i<tuplelen; i++) {
                tup[i]=tuples.get(tupid).getValueIdx(i+1);
            }
            
            // Insert tup into the MDD
            MDDNode curnode=top;
            
            for(int i=0; i<tuplelen; i++) {
                int idx=Collections.binarySearch(curnode.values, tup[i]);
                if(idx<0) {
                    // New node needed. 
                    MDDNode newnode=new MDDNode(curnode);
                    if(i==tuplelen-1) {
                        newnode.type=-1;  // tt node.
                    }
                    mddnodes.add(newnode);
                    
                    mklink(curnode, newnode, tup[i], idx);
                    
                    curnode=newnode;
                }
                else {
                    curnode=curnode.links.get(idx);
                }
            }
            assert curnode.type==-1;
        }
        
        // Label all nodes with a unique integer. 
        for(int i=0; i<mddnodes.size(); i++) {
            mddnodes.get(i).id=i;
        }
        
        // MDD is a trie, start merging from the leaves upwards. 
        
        compress_from_leaves(mddnodes, top, tuplelen);
        
        return new Pair<MDDNode, ArrayList<MDDNode>>(top, mddnodes);
    }
    
    private static void mklink(MDDNode curnode, MDDNode newnode, long value, int idx) {
        curnode.values.add(-(idx+1), value);
        curnode.links.add(-(idx+1), newnode);
    }
    
    private static void compress_from_leaves(ArrayList<MDDNode> mddnodes, MDDNode top, int tuplelen) {
        for(int layer=tuplelen; layer>=0; layer--) {
            ArrayList<MDDNode> nodelist=new ArrayList<MDDNode>();
            find_layer(0, layer, top, nodelist);
            
            // Use stupid algorithm to find duplicates. 
            
            for(int i=0; i<nodelist.size(); i++) {
                for(int j=i+1; j<nodelist.size(); j++) {
                    boolean match=true;
                    MDDNode n1=nodelist.get(i);
                    MDDNode n2=nodelist.get(j);
                    
                    if(n1.type != n2.type) {
                        match=false;
                    }
                    if(n1.links.size()!=n2.links.size()) {
                        match=false;
                    }
                    for(int k=0; k<n1.links.size() && match; k++) {
                        if(n1.links.get(k) != n2.links.get(k) || n1.values.get(k) != n2.values.get(k)) {
                            match=false;
                        }
                    }
                    
                    if(match) {
                        // Delete nodelist[j]
                        MDDNode todelete = nodelist.get(j);
                        
                        nodelist.set(j, nodelist.get(nodelist.size()-1));
                        nodelist.remove(nodelist.size()-1);
                        j--;
                        
                        mddnodes.set(todelete.id, mddnodes.get(mddnodes.size()-1));
                        mddnodes.remove(mddnodes.size()-1);
                        
                        if(todelete.id != mddnodes.size()) {
                            // If we didn't just delete the last element, fix the id.
                            mddnodes.get(todelete.id).id=todelete.id;
                        }
                        
                        ArrayList<MDDNode> parlinks=todelete.parent.links;
                        for(int k=0; k<parlinks.size(); k++) {
                            if(parlinks.get(k)==todelete) {
                                todelete.parent.links.set(k, nodelist.get(i));
                            }
                        }
                    }
                }
            }
        }
        
        //  Check labels of nodes. 
        for(int i=0; i<mddnodes.size(); i++) {
            assert mddnodes.get(i).id==i;
        }
    }
    
    private static void find_layer(int currentlayer, int targetlayer, MDDNode curnode, ArrayList<MDDNode> nodelist) {
        if(currentlayer < targetlayer) {
            for(int i = 0; i < curnode.links.size(); i++) {
                find_layer(currentlayer + 1, targetlayer, curnode.links.get(i), nodelist);
            }
        }
        else {
            assert currentlayer==targetlayer;
            nodelist.add(curnode);
        }
    }
    
    public static void encodeMDDSAT(Sat satModel, ArrayList<ASTNode> vars, MDDNode top, ArrayList<MDDNode> mddnodes) throws IOException {
        //  GenMiniSAT encoding. 
        //  Introduce a SAT variable for each node
        long[] satVars=new long[mddnodes.size()];
        
        for(int i=0; i<mddnodes.size(); i++) {
            satVars[i]=satModel.createAuxSATVariable();
        }
        
        // Iterate for layers except last layer which should have no links. 
        for(int layer=0; layer<vars.size(); layer++) {
            ASTNode var=vars.get(layer);  // The relevant CP variable for transition from layer to layer+1. 
            ArrayList<Intpair> dom=var.getIntervalSetExp();
            
            ArrayList<MDDNode> layerlist=new ArrayList<MDDNode>();
            find_layer(0, layer, top, layerlist);
            
            HashSet<Long> valsseen=new HashSet<Long>();
            
            for(int i=0; i<layerlist.size(); i++) {
                MDDNode n=layerlist.get(i);
                
                ArrayList<Long> m3=new ArrayList<Long>();
                ArrayList<Long> m4=new ArrayList<Long>();
                
                valsseen.clear();
                
                for(int j=0; j<n.links.size(); j++) {
                    MDDNode nchild=n.links.get(j);
                    
                    // Clause M1
                    satModel.addClause(satVars[nchild.id], -var.directEncode(satModel, n.values.get(j)), -satVars[n.id]);
                    
                    // Clause M2
                    satModel.addClause(-satVars[nchild.id], -var.directEncode(satModel, n.values.get(j)), satVars[n.id]);
                    
                    // Clause M3
                    m3.add(-satVars[nchild.id]);
                    
                    // Clause M4
                    m4.add(satVars[nchild.id]);
                    
                    valsseen.add(n.values.get(j));
                }
                
                //  Iterate through any values of var that have not been done yet
                //  Implicit edges to the FF node. 
                for(int j=0; j<dom.size(); j++) {
                    for(long val=dom.get(j).lower; val<=dom.get(j).upper; val++) {
                        if(! valsseen.contains(val)) {
                            //  Child is the FF node, set to false.
                            // Clause M1
                            satModel.addClause(-var.directEncode(satModel, val), -satVars[n.id]);
                            
                            // Clause M2 satisfied.
                            // Clause M3 add a 'true'
                            m3.add(satModel.getTrue());
                            
                            // Clause M4 -- would add a 'false' literal.
                        }
                    }
                }
                
                m3.add(satVars[n.id]);
                satModel.addClause(m3);
                
                m4.add(-satVars[n.id]);
                satModel.addClause(m4);
            }
        }
        
        //  Assert tt.
        for(int i=0; i<mddnodes.size(); i++) {
            if(mddnodes.get(i).type==-1) {
                satModel.addClause(satVars[mddnodes.get(i).id]);
            }
            if(mddnodes.get(i).type==-2) {
                satModel.addClause(-satVars[mddnodes.get(i).id]);
            }
        }
        
        // Assert top.
        satModel.addClause(satVars[top.id]);
    }
}