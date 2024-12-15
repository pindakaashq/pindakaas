package savilerow.pb;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2018 Jordi Coll, Peter Nightingale
    
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
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.TreeSet;

import savilerow.*;
import savilerow.expression.Intpair;
import savilerow.model.Sat;

public class RGGT {
    
    //  Tree node.
    static class RGGTNode {
        public RGGTNode left, right, parent;
        public ArrayList<Long> values;
        
        public ArrayList<Intpair> intervals;
        
        public ArrayList<Long> literals;   //  SAT literals the intervals are associated to.
        
        public RGGTNode(RGGTNode _left, RGGTNode _right) {
            left=_left;
            right=_right;
            parent=null;
            values=new ArrayList<Long>();
            intervals=new ArrayList<Intpair>();
            literals=new ArrayList<Long>();
        }
        
        //  For caching mergeValues -- not complete equality, ignores everything except the values. 
        @Override
        public int hashCode() {
            return values.hashCode();
        }
        @Override
        public boolean equals(Object o) {
            if(o instanceof RGGTNode) {
                return ((RGGTNode)o).values.equals(values);
            }
            return false;
        }
        
        public void makeIntervals(ArrayList<RGGTNode> tree, long K, boolean reduce) {
            if(reduce) {
                // Assumes parent already has a set of intervals. 
                // Uses values of the sibling. 
                
                //  Singleton interval to start with.
                intervals.add(new Intpair(values.get(0), values.get(0)));
                
                //  Iterate through values, checking each one 
                for(int i=0; i<values.size()-1; i++) {
                    long lower=values.get(i);
                    long upper=values.get(i+1);
                    
                    boolean split=false;
                    
                    ArrayList<Long> siblingvals=( (parent.left==this) ? parent.right.values : parent.left.values); 
                    for(int j=0; j<siblingvals.size(); j++) {
                        long sibval=siblingvals.get(j);
                        
                        // For this sibling value, does the difference between lower and upper shift
                        // to a different interval in the parent?
                        
                        long seekval=sibval+lower;
                        
                        // Lazy loop for now -- should be binary search.
                        // Not all combinations of lower, upper and sibling value will end up in an
                        // interval in the parent -- because with -rggt-mutex, some combinations are filtered out. 
                        // So make a fake interval if it lands between or above the set of intervals. 
                        Intpair parentInterval=null;
                        ArrayList<Intpair> parints=parent.intervals;
                        for(int k=0; k<parints.size(); k++) {
                            if(parints.get(k).lower<=seekval && parints.get(k).upper>=seekval) {
                                parentInterval=parints.get(k);
                                break;
                            }
                            else if(parints.get(k).lower==K+1 && seekval>=K+1) {
                                parentInterval=parints.get(k);
                                break;
                            }
                            // Falls between intervals
                            else if(k<parints.size()-1 && parints.get(k).upper<seekval && parints.get(k+1).lower>seekval) {
                                parentInterval=new Intpair(parints.get(k).upper+1, parints.get(k+1).lower-1);
                                break;
                            }
                        }
                        if(parentInterval==null) {
                            assert seekval>parints.get(parints.size()-1).upper;
                            parentInterval=new Intpair(parints.get(parints.size()-1).upper+1, Long.MAX_VALUE);
                        }
                        
                        //  Test the upper bound plus sibling value, does that fall in the same interval?
                        long val2=sibval+upper;
                        if(seekval<=K && (val2<parentInterval.lower || val2>parentInterval.upper)) {
                            split=true;
                            break;
                        }
                    }
                    
                    if(split) {
                        // Start a new interval with upper. 
                        intervals.add(new Intpair(upper, upper));
                    }
                    else {
                        // Join upper onto the last interval.
                        intervals.get(intervals.size()-1).upper=upper;
                    }
                }
            }
            else {
                // Don't do reduction -- one interval for each value. 
                for(int i=0; i<values.size(); i++) {
                    intervals.add(new Intpair(values.get(i), values.get(i)));
                }
            }
        }
        
        public int getDepth() {
            if(parent==null) {
                return 1;
            }
            else {
                return parent.getDepth()+1;
            }
        }
        
        public String toString() {
            return "RGGTNode. "+values+"\n"+intervals+"\nliterals:"+literals;
        }
    }
    
    // Sort for smallest interval first
    static class CompareRGGTNode implements Comparator<RGGTNode> {
        public int compare(RGGTNode x, RGGTNode y) {
            long ubx=x.values.get(x.values.size()-1);
            long uby=y.values.get(y.values.size()-1);
            
            if(ubx<uby) {
                return -1;
            }
            else if(ubx>uby) {
                return 1;
            }
            return 0;
        }
    }
    
    private static int pol=1;
    
    public static void addAMOPBGeneralizedTotalizer(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int K, boolean reduce, Sat satModel) throws IOException {
        //  Badly co-sort Q and X.
        for(int i=0; i<Q.size(); i++) {
            ArrayList<Integer> qa=Q.get(i);
            ArrayList<Long> xa=X.get(i);
            
            //  Cosort qa and xa by insertion sort. 
            for(int j=1; j<qa.size(); j++) {
                for(int k=j-1; k>=0; k--) {
                    if(qa.get(k+1)<qa.get(k)) {
                        //  Swap
                        Integer tmpq=qa.get(k);
                        qa.set(k, qa.get(k+1));
                        qa.set(k+1, tmpq);
                        
                        Long tmpx=xa.get(k);
                        xa.set(k, xa.get(k+1));
                        xa.set(k+1, tmpx);
                    }
                }
            }
        }
        
        ArrayList<RGGTNode> tree=null;
        int n = X.size();
        boolean repeatReduce=true;
        
        while(repeatReduce) {
            repeatReduce=false;
            n = X.size();
            
            tree = new ArrayList<RGGTNode>(n);
            
            //  Leaf nodes on the left (indexes 0 to n-1)
            //  Fill leaf nodes with values
            //  Literals left empty for now. 
            for(int i = 0; i < n; i++) {
                tree.add(new RGGTNode(null, null));
                
                tree.get(i).values.add(0L);
                
                for(int j = 0; j < Q.get(i).size(); j++) {
                    int q = Q.get(i).get(j);
                    if(q!=0 && (j==0 || q!=Q.get(i).get(j-1))) {
                        //  Non-zero coeff and different to previous coeff.
                        tree.get(i).values.add((long)q);
                    }
                }
            }
            
            //  Create intermediate node with greatest proportional reduction in values compared to the product of the two children.
            ArrayList<RGGTNode> todo=new ArrayList<>(tree);  // copy tree into todo (shallow copy)
            
            /*if(CmdFlags.rggt_mutex) {
                // Take pairs of leaf nodes with additional mutexes between
                // values and combine to a parent node. 
                
                while(todo.size()>1) {
                    int i1=-1;
                    int i2=-1;
                    int maxMutexes=-1;
                    double minrat=1.0;
                    
                    for(int i=0; i<todo.size()-1; i++) {
                        if(todo.get(i)!=null && todo.get(i).left==null) {
                            for(int j=i+1; j<todo.size(); j++) {
                                if(todo.get(j)!=null && todo.get(j).left==null) {
                                    // i and j are indices into X and Q, as well as todo.
                                    
                                    // Heuristic 1, count the mutexes. 
                                    //int mutexes=0;
                                    //for(int lit1idx=0; lit1idx<X.get(i).size(); lit1idx++) {
                                    //    for(int lit2idx=0; lit2idx<X.get(j).size(); lit2idx++) {
                                    //        if(AMODetect.isMutex(satModel, X.get(i).get(lit1idx), X.get(j).get(lit2idx))) {
                                    //            mutexes++;
                                    //        }
                                    //    }
                                    //}
                                    //if(mutexes>maxMutexes) {
                                    //    i1=i;
                                    //    i2=j;
                                    //    maxMutexes=mutexes;
                                    //}
                                    
                                    // Heuristic 2, minimise ratio between merge values mutex size and regular merge values size. 
                                    
                                    ArrayList<Long> tmp=new ArrayList<>();
                                    mergeValuesMutex(satModel, X.get(i), X.get(j), Q.get(i), Q.get(j), todo.get(i).values, todo.get(j).values, tmp, K);  // Populate n3.values
                                    
                                    double mvmsize=tmp.size();
                                    
                                    tmp.clear();
                                    mergeValues(todo.get(i).values, todo.get(j).values, tmp, K);
                                    
                                    if( (mvmsize/((double)tmp.size())) < minrat) {
                                        i1=i;
                                        i2=j;
                                        minrat=(mvmsize/((double)tmp.size()));
                                    }
                                }
                            }
                        }
                    }
                    
                    //if(maxMutexes<=0) {
                    //    break;
                    //}
                    if(minrat==1.0) {
                        break;
                    }
                    
                    RGGTNode n1=todo.get(i1);
                    RGGTNode n2=todo.get(i2);
                    
                    todo.set(i1, null);
                    todo.set(i2, null);
                    
                    RGGTNode n3=new RGGTNode(n1, n2);
                    n1.parent=n3;
                    n2.parent=n3;
                    
                    mergeValuesMutex(satModel, X.get(i1), X.get(i2), Q.get(i1), Q.get(i2), n1.values, n2.values, n3.values, K);  // Populate n3.values
                    
                    tree.add(n3);
                    todo.add(n3);
                    //System.out.println("Added node: "+n3+" for mutexes thing");
                }
                
                /// remove nulls from todo without changing order.
                for(int i=0; i<todo.size(); i++) {
                    if(todo.get(i)==null) {
                        todo.remove(i);
                        i--;
                    }
                }
            }*/
            
            HashMap<Pair<RGGTNode, RGGTNode>, Double> cached_rat=new HashMap<>();
            boolean first_pass = true;
            while(todo.size()>1) {
                // Compute new ratios
                for(int i=0; i<todo.size()-1; i++) {
                    //If first, time, compute all the ratios
                    if(first_pass) {
                        for(int j=i+1; j<todo.size(); j++) {
                            ArrayList<Long> testvals=new ArrayList<Long>();
                            mergeValues(todo.get(i).values, todo.get(j).values, testvals, K);
                            double rat=((double)testvals.size())/(todo.get(i).values.size()*todo.get(j).values.size());
                            cached_rat.put(new Pair<RGGTNode, RGGTNode>(todo.get(i), todo.get(j)), rat);
                        }
                    }
                    // Otherwise, there is only need to compute the ratio w.r.t. the newly inserted node
                    else {
                        int j = todo.size()-1;
                        ArrayList<Long> testvals=new ArrayList<Long>();
                        mergeValues(todo.get(i).values, todo.get(j).values, testvals, K);
                        double rat=((double)testvals.size())/(todo.get(i).values.size()*todo.get(j).values.size());
                        cached_rat.put(new Pair<RGGTNode, RGGTNode>(todo.get(i), todo.get(j)), rat);
                    }
                }
                first_pass=false;
                
                //  Find pair of nodes with the best ratio
                
                int i1=-1;
                int i2=-1;
                double bestRatio=Double.MAX_VALUE;
                for(int i=0; i<todo.size()-1; i++) {
                    if(todo.get(i) != null) {
                        for(int j=i+1; j<todo.size(); j++) {
                            if(todo.get(j) != null) {
                                double rat=cached_rat.get(new Pair<RGGTNode, RGGTNode>(todo.get(i), todo.get(j)));
                                
                                if(rat<bestRatio) {
                                    i1=i;
                                    i2=j;
                                    bestRatio=rat;
                                }
                            }
                        }
                    }
                }
                
                // Really inefficient.
                RGGTNode n1=todo.get(i1);
                RGGTNode n2=todo.get(i2);
                
                todo.remove(i2);
                todo.remove(i1);
                
                //System.out.println("Merging "+n1.values+" and "+n2.values);
                
                RGGTNode n3=new RGGTNode(n1, n2);
                n1.parent=n3;
                n2.parent=n3;
                
                if(CmdFlags.rggt_mutex && tree.size()==X.size()) {
                    //   tree.size()==X.size() means this is the first pair. 
                    //mergeValues(n1.values, n2.values, n3.values, K);
                    //System.out.println("Merge without mutex: "+n3.values);
                    
                    mergeValuesMutex(satModel, X.get(i1), X.get(i2), Q.get(i1), Q.get(i2), n1.values, n2.values, n3.values, K);  // Populate n3.values
                    //System.out.println("Merge with mutex   : "+n3.values);
                }
                else {
                    mergeValues(n1.values, n2.values, n3.values, K);  // Populate n3.values
                }
                
                tree.add(n3);
                todo.add(n3);
            }
            
            //  Now tree has values, but intervals and literals are empty
            //  except bottom layer which has literals populated. 
            
            //  Start to populate intervals from the root. 
            
            RGGTNode root=tree.get(tree.size()-1);
            
            //  Check the tree is not trivial here...
            
            
            long lb=root.values.get(0);
            long ub=root.values.get(root.values.size()-1);
            if(ub==K+1) {
                ub=root.values.get(root.values.size()-2);
            }
            root.intervals.add(new Intpair(lb, ub));
            if(root.values.get(root.values.size()-1)==K+1) {
                root.intervals.add(new Intpair(K+1, K+1));
            }
            
            // Go down the tree from root to leaves, creating the interval sets.
            // Parent must be processed before its children.
            
            for(int i=tree.size()-2; i>=0; i--) {
                tree.get(i).makeIntervals(tree, K, reduce);
            }
            
            // Check for trivial leaf nodes 
            // This could be much more interesting. Leaf nodes that have non-singleton
            // intervals could be have coefficients changed to turn the interval into a 
            // single value. 
            
            for(int i=n-1; i>=0; i--) {
                if(tree.get(i).intervals.size()==1) {
                    //  Single interval. Remove the AMO group.
                    //  This definitely helps -- reduces number of internal tree nodes. 
                    Q.remove(i);
                    X.remove(i);
                    repeatReduce=true;
                }
                //  I suspect the following may not help except by
                //  changing the heuristic order of combining nodes. 
                else if(tree.get(i).intervals.size()<tree.get(i).values.size()) {
                    ArrayList<Integer> qvals=Q.get(i);
                    ArrayList<Intpair> intervals=tree.get(i).intervals;
                    int intervalidx=0;
                    
                    for(int qidx=0; qidx<qvals.size(); qidx++) {
                        long value=qvals.get(qidx);
                        Intpair interval=intervals.get(intervalidx);
                        while(value>interval.upper) {
                            intervalidx++;
                            interval=intervals.get(intervalidx);
                        }
                        assert value>=interval.lower && value<=interval.upper;
                        if(value!=interval.lower) {
                            if(interval.lower==0) {
                                //  Indistinguishable from 0 -- bin the term. 
                                qvals.remove(qidx);
                                X.get(i).remove(qidx);
                                qidx--;
                            }
                            else {
                                qvals.set(qidx, (int)interval.lower);  //  Heuristic -- push indistinguishable values down to be the same value.
                            }
                        }
                    }
                    
                    repeatReduce=true;
                }
            }
            
            //if(repeatReduce) System.out.println("Restarting");
        }  // End of while loop.
        
        //  Dump tree statistics. 
        if(CmdFlags.rggt_stats) {
            for(int i=tree.size()-1; i>=0; i--) {
                RGGTNode node=tree.get(i);
                System.out.println("RGGT node depth: "+node.getDepth() 
                    + ", values: "+ node.values.size() 
                    + ", intervals: "+ node.intervals.size());
            }
        }
        
        //  Encode the tree.
        //  SAT variables correspond to intervals (>= lower bound ofinterval).
        
        for(int i=n; i<tree.size(); i++) {
            assert tree.get(i).intervals.get(0).lower==0;
            tree.get(i).literals.add(satModel.getTrue());
            
            //  Skip the first interval. 
            for(int j=1; j<tree.get(i).intervals.size(); j++) {
                //long l=promote(j, tree.get(i), K);
                //if(l>-1) {
                //    tree.get(i).literals.add(l);
                //}
                //else {
                long v = satModel.createAuxSATVariable();
                tree.get(i).literals.add(v*pol);
                //}
            }
        }
        
        //  Fill in literals for the leaf nodes.
        for(int i=0; i<n; i++) {
            RGGTNode l=tree.get(i);
            
            for(int j=0; j<l.intervals.size(); j++) {
                Intpair interval=l.intervals.get(j);
                if(interval.lower==0) {
                    l.literals.add(satModel.getTrue());
                }
                else {
                    //  Find all coeffs that fall within the interval
                    ArrayList<Integer> qi=Q.get(i);
                    ArrayList<Long> xi=X.get(i);
                    
                    int count=0;
                    long last=0;
                    
                    for(int k=0; k<qi.size(); k++) {
                        if(qi.get(k)>=interval.lower && qi.get(k)<=interval.upper) {
                            count++;
                            last=xi.get(k);
                        }
                    }
                    
                    if(count>1) {
                        long aux=satModel.createAuxSATVariable();
                        l.literals.add(aux);
                        
                        for(int k=0; k<qi.size(); k++) {
                            if(qi.get(k)>=interval.lower && qi.get(k)<=interval.upper) {
                                satModel.addClause(-xi.get(k), aux);
                            }
                        }
                    }
                    else {
                        assert count==1;
                        l.literals.add(last);
                    }
                }
            }
            assert l.literals.size()==l.intervals.size();
        }
        
        for(int i=n; i<tree.size(); i++) {
            RGGTNode l=tree.get(i).left;
            RGGTNode r=tree.get(i).right;
            
            for(int j=0; j<l.intervals.size(); j++) {
                for(int k = 0; k < r.intervals.size(); k++) {
                    // Calculate the value from the lower bounds of the two intervals. 
                    long x = Math.min(l.intervals.get(j).lower+r.intervals.get(k).lower,K+1);
                    
                    //  Find the interval that x belongs to in the parent.
                    int paridx=findInterval(x, tree.get(i).intervals);
                    
                    if(CmdFlags.rggt_reduce && paridx>=0 && j>0 && l.left!=null && tree.get(i).literals.get(paridx)!=satModel.getTrue() && findInterval(Math.min(l.intervals.get(j-1).lower+r.intervals.get(k).lower,K+1), tree.get(i).intervals)==paridx) {
                        //  Clause already generated for j-1, k
                        //  add binary clause for j -> j-1.
                        satModel.addClause(-l.literals.get(j), l.literals.get(j-1));
                        continue;
                    }
                    
                    if(CmdFlags.rggt_reduce && paridx>=0 && k>0 && r.left!=null && tree.get(i).literals.get(paridx)!=satModel.getTrue() && findInterval(Math.min(l.intervals.get(j).lower+r.intervals.get(k-1).lower,K+1), tree.get(i).intervals)==paridx) {
                        //  Clause already generated for j, k-1
                        satModel.addClause(-r.literals.get(k), r.literals.get(k-1));
                        continue;
                    }
                    
                    if(paridx>=0) {
                        if(!CmdFlags.rggt_mutex || !AMODetect.isMutex(satModel, l.literals.get(j), r.literals.get(k))) {
                            satModel.addClause(-l.literals.get(j), -r.literals.get(k), tree.get(i).literals.get(paridx));
                        }
                        else {
                            // The two literals are mutex -- add mutex explicitly. 
                            satModel.addClause(-l.literals.get(j), -r.literals.get(k));
                        }
                    }
                    else {
                        ///  No corresponding interval in parent -- pair of literals must be mutex. 
                        assert CmdFlags.rggt_mutex; // && AMODetect.isMutex(satModel, l.literals.get(j), r.literals.get(k));
                        satModel.addClause(-l.literals.get(j), -r.literals.get(k));
                    }
                }
            }
        }
        
        // Assert that the sum is <=K.
        // If the top interval of the root node contains K+1, then assert ! the top interval. 
        // If -rggt-mutex is used, the root node may not have value K+1. 
        
        int i=tree.size()-1;
        if(tree.get(i).intervals.get(tree.get(i).intervals.size()-1).lower==K+1) {
            satModel.addClause(-tree.get(i).literals.get(tree.get(i).literals.size()-1));
        }
    }
    
    private static int findInterval(long x, ArrayList<Intpair> parint) {
        //  Binary search for interval in parent. 
        int paridx=0;
        int lidx=0;
        int ridx=parint.size()-1;
        boolean found=false;
        while(lidx <= ridx && !found) {
            paridx=(lidx+ridx)/2;
            if(x < parint.get(paridx).lower) {
                ridx = paridx-1;
            }
            else if(x > parint.get(paridx).upper) {
                lidx = paridx+1;
            }
            else {
                found=true;
            }
        }
        
        if(!found) {
            return -1;
        }
        else {
            return paridx;
        }
    }
    
    //  Given a current node (with children) and an index of an interval in that node, can
    //  a literal be promoted from one of its children? i.e. one interval on one side, all intervals on the other.
    private static long promote(int paridx, RGGTNode curnode, long K) {
        RGGTNode l=curnode.left;
        RGGTNode r=curnode.right;
        
        HashSet<Integer> lset=new HashSet<Integer>();
        HashSet<Integer> rset=new HashSet<Integer>();
        
        for(int j=0; j<l.intervals.size(); j++) {
            for(int k = 0; k < r.intervals.size(); k++) {
                // Calculate the value from the lower bounds of the two intervals. 
                long x2 = Math.min(l.intervals.get(j).lower+r.intervals.get(k).lower,K+1);
                
                //  Find the interval that x2 belongs to in the parent.
                int paridx2=findInterval(x2, curnode.intervals);
                
                if(paridx==paridx2) {
                    lset.add(j);
                    rset.add(k);
                    //if(lset.size()>1 && rset.size()>1) {
                    //    return -1;
                    //}
                }
            }
        }
        
        System.out.println(""+paridx+", curnode: "+curnode.intervals);
        System.out.println("left :"+l.intervals);
        System.out.println("right:"+r.intervals);
        
        System.out.println(lset);
        System.out.println(rset);
        
        if(lset.size()==1 && rset.size()==r.intervals.size()) {
            //  Whatever the value (interval) of r, then lset is the one interval so promote that.  
            int lidx=((Integer)lset.toArray()[0]);
            return l.literals.get(lidx);
        }
        if(rset.size()==1 && lset.size()==l.intervals.size()) {
            //  Whatever the value (interval) of r, then lset is the one interval so promote that.  
            int ridx=((Integer)rset.toArray()[0]);
            return r.literals.get(ridx);
        }
        
        return -1;
    }
    
    // Merge n1, n2 into n3
    private static void mergeValues(ArrayList<Long> n1, ArrayList<Long> n2, ArrayList<Long> n3, long K) {
        TreeSet<Long> t=new TreeSet<>();
        for(int j=0; j < n1.size(); j++) {
            for(int k = 0; k < n2.size(); k++) {
                long x = Math.min(n1.get(j)+n2.get(k), K+1);
                t.add(x);
            }
        }
        n3.clear();
        n3.addAll(t);
    }
    
    // Merge n1, n2 into n3
    private static void mergeValuesMutex(Sat satModel, ArrayList<Long> x1, ArrayList<Long> x2, ArrayList<Integer> q1, ArrayList<Integer> q2, ArrayList<Long> n1, ArrayList<Long> n2, ArrayList<Long> n3, long K) {
        TreeSet<Long> t=new TreeSet<>();
        for(int j=0; j < n1.size(); j++) {
            for(int k = 0; k < n2.size(); k++) {
                long value1=n1.get(j);
                long value2=n2.get(k);
                
                long x = Math.min(value1+value2, K+1);
                
                if(value1==0 || value2==0) {
                    //  0 can't be mutex with any value. 
                    t.add(x);
                }
                else {
                    // Check if value1 and value2 cannot occur together
                    boolean mutex=true;
                    for(int i1=0; i1<q1.size() && mutex; i1++) {
                        if(q1.get(i1)==value1) {
                            for(int i2=0; i2<q2.size() && mutex; i2++) {
                                if(q2.get(i2)==value2) {
                                    if(!AMODetect.isMutex(satModel, x1.get(i1), x2.get(i2))) {
                                        mutex=false;
                                    }
                                }
                            }
                        }
                    }
                    
                    if(mutex) {
                        //System.out.println("Saved value: "+x);
                    }
                    
                    if(!mutex) {
                        t.add(x);
                    }
                }
            }
        }
        n3.clear();
        n3.addAll(t);
    }
}