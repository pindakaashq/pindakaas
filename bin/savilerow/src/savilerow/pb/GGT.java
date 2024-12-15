package savilerow.pb;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Jordi Coll, Peter Nightingale
    
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
import java.util.HashMap;
import java.util.Map;

import savilerow.model.Sat;

public class GGT {
    public static void addAMOPBGeneralizedTotalizer(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int K, Sat satModel) throws IOException {
        int n = X.size();
        
        ArrayList<ArrayList<Integer>> tree = new ArrayList<ArrayList<Integer>>(2*n-1);    //  Was std::vector<int> * tree
        for(int i=0; i<2*n-1; i++) tree.add(new ArrayList<Integer>());
        
        ArrayList<ArrayList<Long>> treevars = new ArrayList<ArrayList<Long>>(2*n-1);
        for(int i=0; i<2*n-1; i++) treevars.add(new ArrayList<Long>());
        
        ArrayList<HashMap<Integer, Long>> treevarsmap = new ArrayList<>(n-1);
        for(int i=0; i<n-1; i++) {
            treevarsmap.add(new HashMap<Integer, Long>());
        }
        
        //Fill tree nodes with coefficients
        for(int i = 0; i < n; i++) {
            int idx = n-1+i;
            tree.get(idx).clear();
            treevars.get(idx).clear();
            HashMap<Integer, Integer> count = new HashMap<>();
            HashMap<Integer, Long> lit = new HashMap<>();
            for(int j = 0; j < Q.get(i).size(); j++) {
                int q = Q.get(i).get(j);
                if(q!=0) {
                    if(! count.containsKey(q)) {
                        count.put(q, 1);
                        lit.put(q, X.get(i).get(j));
                    }
                    else {
                        if(count.get(q)==1) {
                            long v = satModel.createAuxSATVariable();
                            satModel.addClause(-lit.get(q), v);
                            lit.put(q, v);
                        }
                        satModel.addClause(-X.get(i).get(j), lit.get(q));
                        count.put(q, count.get(q)+1);
                    }
                }
            }
            for(Map.Entry<Integer, Long> p : lit.entrySet()) {
                tree.get(idx).add(p.getKey());
                treevars.get(idx).add(p.getValue());
            }
            tree.get(idx).add(0);
        }
        
        for(int i = n-2; i >= 0; i--) {
            tree.get(i).clear();
            for(int j = 0; j < tree.get(lchild(i)).size(); j++) {
                for(int k = 0; k < tree.get(rchild(i)).size(); k++) {
                    int x = Math.min(tree.get(lchild(i)).get(j)+tree.get(rchild(i)).get(k),K+1);
                    if(!existsSorted(tree.get(i), x)) {
                        insertSorted(tree.get(i), x);
                    }
                }
            }
        }
        
        //Simplify the tree with the unnecessary values
        
        //Simplify the root
        if(tree.get(0).get(0) < K+1) {
            return;
        }
        
        resizeArrayList(tree.get(0), 2);
        tree.get(0).set(1, 0);
        
        //Encode the tree
        for(int i = n-2; i >= 0; i--) {
            for(int j = 0; j < tree.get(i).size()-1; j++) {
                long v = satModel.createAuxSATVariable();
                treevars.get(i).add(v);
                treevarsmap.get(i).put(tree.get(i).get(j), v);
            }
            
            int l = lchild(i);
            int r = rchild(i);
            
            for(int j = 0; j < tree.get(l).size(); j++) {
                for(int k = 0; k < tree.get(r).size(); k++) {
                    int x = Math.min(tree.get(l).get(j)+tree.get(r).get(k),K+1);
                    if(treevarsmap.get(i).containsKey(x)) {
                        if(j<tree.get(l).size()-1 || k < tree.get(r).size()-1) {
                            if(j == tree.get(l).size()-1) {
                                satModel.addClause(-treevars.get(r).get(k), treevarsmap.get(i).get(x));
                            }
                            else if(k == tree.get(r).size()-1) {
                                satModel.addClause(-treevars.get(l).get(j), treevarsmap.get(i).get(x));
                            }
                            else {
                                satModel.addClause(-treevars.get(l).get(j), -treevars.get(r).get(k), treevarsmap.get(i).get(x));
                            }
                        }
                    }
                }
            }
        }
        
        //Negate that the sum is greater than K
        if(!tree.get(0).isEmpty()) {
            satModel.addClause(-treevars.get(0).get(0));
        }
    }
    
    private static int lchild(int i){
        return 2*i+1;
    }
    
    private static int rchild(int i){
        return 2*i+2;
    }
    
    /*
    //  These two have the vectors in increasing order, when they need to 
    //  be decreasing. 
    private static boolean existsSorted(ArrayList<Integer> a, int x) {
        return Collections.binarySearch(a, (Integer)x)>=0;
    }
    
    private static void insertSorted(ArrayList<Integer> a, int x) {
        int i = Collections.binarySearch(a, x);
        assert i < 0;
        a.add(-i-1, x);
    }*/
    
    private static void resizeArrayList(ArrayList<Integer> a, int n) {
        while(a.size()>n) {
            a.remove(a.size()-1);
        }
        while(a.size()<n) {
            a.add(0);
        }
    }
    
    private static boolean existsSorted(ArrayList<Integer> v, int x) {
        for(int i = 0; i < v.size(); i++) {
            if(v.get(i) == x) {
                return true;
            }
            else if(v.get(i) < x) {
                return false;
            }
        }
        return false;
    }
    
    private static void insertSorted(ArrayList<Integer> v, int x) {
        v.add(0);
        for(int i = v.size()-1; i > 0; i--) {
            if(v.get(i-1) < x) {
                v.set(i, v.get(i-1));
            }
            else {
                v.set(i, x);
                return;
            }
        }
        v.set(0, x);
    }
}