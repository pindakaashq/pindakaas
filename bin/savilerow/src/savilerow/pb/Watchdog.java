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
import java.util.Collections;
import java.util.HashMap;
import java.util.TreeSet;

import savilerow.Pair;
import savilerow.expression.Intpair;
import savilerow.model.Sat;

public class Watchdog {
    
    // This function checked 13/3/2021
    private static long addPolynomialWatchdog(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int K, boolean useSorter, Sat satModel) throws IOException {
        int n = Q.size();
        
        //This encoding is for < K instead of <= K
        K+=1;
        
        int max = 0;
        for(ArrayList<Integer> q : Q) {
            for(int qi : q) {
                if(qi > max) {
                    max = qi;
                }
            }
        }
        
        int p = floorlog2(max);
        int p2 = exp2(p);
        int m = K / p2;
        if(K%p2 != 0) {
            m++;
        }
        int T = (m*p2) - K;
        
        ArrayList<ArrayList<Long>> B=new ArrayList<>(p+1);  //Buckets
        for(int i=0; i<p+1; i++) {
            B.add(new ArrayList<Long>());
        }
        
        for(int k = 0; k <= p; k++) {
            for(int i = 0; i < n; i++) {
                boolean used = false;
                boolean created = false;
                long vk=0L;  //  Initial value, should never be used.
                for(int j = 0; j < Q.get(i).size(); j++){
                    if(nthBit(Q.get(i).get(j),k)) {
                        if(!used) {
                            vk = X.get(i).get(j);
                            used = true;
                        }
                        else {
                            if(!created) {
                                long aux = satModel.createAuxSATVariable();
                                satModel.addClause(-vk, aux);
                                vk = aux;
                                created=true;
                            }
                            satModel.addClause(-X.get(i).get(j), vk);
                        }
                    }
                }
                if(used) {
                    B.get(k).add(vk);
                }
            }
        }
        
        ArrayList<Long> S = new ArrayList<Long>();
        ArrayList<Long> Shalf = new ArrayList<Long>();
        
        for(int i = 0; i <= p; i++) {
            S.clear();
            ArrayList<Long> U = new ArrayList<>();
            if(useSorter) {
                addSorting(B.get(i), U, true, false, satModel);
            }
            else {
                addTotalizer(B.get(i), U, satModel);
            }
            
            if(i==0) {
                // S=U
                copyArrayList(U, S);
            }
            else {
                if(useSorter) {
                    addMerge(U,Shalf,S, true,false, satModel);
                }
                else {
                    if(false) {
                        if(i<p) {
                            addQuadraticMerge2(U, Shalf, S, satModel, !nthBit(T,i));
                        }
                        else {
                            //  Last one -- only one output bit required
                            addQuadraticMergeOne(U, Shalf, S, satModel, (m-1)+(nthBit(T,i)?1:0));
                            //System.out.println(S.size()+", "+(m-1));
                        }
                    }
                    else {
                        addQuadraticMerge(U, Shalf, S, satModel);
                    }
                }
            }
            if(nthBit(T,i)) {
                S.add(0, satModel.getTrue());
            }
            
            Shalf.clear();
            for(int j = 1; j < S.size(); j+=2) {
                Shalf.add(S.get(j));
            }
        }
        
        return S.get(m-1);
    }
    
    // This function checked 13/3/2021
    public static void addAMOPBGlobalPolynomialWatchdog(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int K, boolean useSorter, Sat satModel) throws IOException {
        satModel.addClause(-addPolynomialWatchdog(Q,X,K,useSorter,satModel));
    }
    
    
    //  The local variant has stronger propagation but is larger.
    public static void addAMOPBNaiveLocalPolynomialWatchdog(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int K, boolean useSorter, Sat satModel) throws IOException {
        if(K==0) {
            for(ArrayList<Long> v : X) {
                for(long l : v) {
                    satModel.addClause(-l);
                }
            }
            return;
        }
        
        else if(K < 0){
            satModel.addClause(-satModel.getTrue());
            return;
        }
        
        int n = Q.size();
        
        int maxsum = 0;
        for(int i = 0; i < n; i++) {
            maxsum += Collections.max(Q.get(i));
        }
        
        if(maxsum <= K) {
            return;
        }
        
        if(n==1) {
            ArrayList<Long> c = new ArrayList<>();
            for(int i = 0; i < Q.get(0).size(); i++) {
                if(Q.get(0).get(i) >= K) {
                    c.add(X.get(0).get(i));
                }
            }
            satModel.addClause(c);
            return;
        }
        
        for(int i = 0; i < n; i++) {
            ArrayList<ArrayList<Integer>> Q2 = new ArrayList<>();  // = Q;
            for(int j=0; j<X.size(); j++) {
                ArrayList<Integer> tmp=new ArrayList<Integer>();
                copyArrayList(Q.get(j), tmp);
                Q2.add(tmp);
            }
            
            ArrayList<ArrayList<Long>> X2 = new ArrayList<>();  //= X;
            for(int j=0; j<X.size(); j++) {
                ArrayList<Long> tmp=new ArrayList<Long>();
                copyArrayList(X.get(j), tmp);
                X2.add(tmp);
            }
            
            Q2.set(i, Q2.get(Q2.size()-1));
            Q2.remove(Q2.size()-1);
            
            X2.set(i, X2.get(X2.size()-1));
            X2.remove(X2.size()-1);
            
            for(int j = 0; j < Q.get(i).size(); j++) {
                HashMap<Integer, Long> watchdog = new HashMap<>();   //  Pointless. Was probably a cache at some point. 
                if(!watchdog.containsKey(Q.get(i).get(j))) {
                    watchdog.put(Q.get(i).get(j), addPolynomialWatchdog(Q2,X2,K-Q.get(i).get(j),useSorter, satModel));
                }
                satModel.addClause(-watchdog.get(Q.get(i).get(j)), -X.get(i).get(j));
            }
        }
    }
    
    //   GLPW
    //   Checked 14/3/2021
    public static void addAMOPBLocalPolynomialWatchdog(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int K, Sat satModel) throws IOException {
        int n = Q.size();
        
        K+=1;
        
        // Maximum of each AMO group
        ArrayList<Integer> max_coefs=new ArrayList<>(n);
        int sum_max_coefs=0;
        
        for(int i=0; i<n; i++) {
            max_coefs.add(Collections.max(Q.get(i)));
            sum_max_coefs+=max_coefs.get(i);
        }
        
        // Overall maximum
        int max=Collections.max(max_coefs);
        
        int p = floorlog2(max);
        int p2 = 1<<p; // 2^p
        
        ArrayList<ArrayList<Long>> B = new ArrayList<>(p+1); //Buckets
        for(int i=0; i<p+1; i++) {
            B.add(new ArrayList<Long>());
        }
        
        ArrayList<ArrayList<Pair<Integer, TreeSet<Integer>>>>  B_inputs = new ArrayList<>(p+1);  //Bucket inputs
        for(int i=0; i<p+1; i++) {
            B_inputs.add(new ArrayList<>());
        }
        
        ArrayList<ArrayList<Integer>> indexesInBuckets = new ArrayList<>(p+1);   //Store which index in each bucket occupies each group
        
        for(int i = 0; i < p+1; i++) {
            indexesInBuckets.add(new ArrayList<Integer>(n));
            for(int j = 0; j < Q.size(); j++) {
                indexesInBuckets.get(i).add(-1);
            }
        }
        
        ArrayList<HashMap<TreeSet<Integer>, Long>> constructedYs = new ArrayList<>(n);
        for(int i=0; i<n; i++) {
            constructedYs.add(new HashMap<>());
        }
        
        // Construct the inputs of the buckets reusing the Y variables already constructed
        for(int k = 0; k <= p; k++) {
            for(int i = 0; i < n; i++) {
                TreeSet<Integer> inputs=new TreeSet<Integer>();
                
                for(int j = 0; j < Q.get(i).size(); j++) {
                    if(nthBit(Q.get(i).get(j), k)) {
                        inputs.add(j);
                    }
                }
                
                if(inputs.size()>0) {
                    long y;
                    if(inputs.size()==1) { //If just one input variable in the group, no need to create a new variable
                        y = X.get(i).get(inputs.first());
                    }
                    else {
                        Long lit=constructedYs.get(i).get(inputs);
                        
                        if(lit==null) { // If not constructed before, add half reifications and store
                            y = satModel.createAuxSATVariable();
                            for(int j : inputs) {
                                satModel.addClause(-X.get(i).get(j), y);
                            }
                            constructedYs.get(i).put(inputs, y);
                        }
                        else { //If already constructed, retrieve
                            y = lit;
                        }
                    }
                    
                    indexesInBuckets.get(k).set(i, B.get(k).size());
                    B.get(k).add(y);
                    B_inputs.get(k).add(new Pair<Integer, TreeSet<Integer>>(i, inputs));
                }
            }
        }
        
        HashMap<TreeSet<Intpair>, ArrayList<Long>> constructedTotalizers=new HashMap<>();
        
        ArrayList<HashMap<TreeSet<Intpair>, ArrayList<Long>>> constructedMergers = new ArrayList<>(p);
        //Bucket 0 does not have a merger, hence size is not p+1.
        for(int i=0; i<p; i++) {
            constructedMergers.add(new HashMap<>());
        }
        
        // Construct circuits for each group. 
        for(int i = 0; i < Q.size(); i++) {
            
            //Complete de circuit with the particlar mergers for each variable 'x_'j' or each variable in group 'i'
            for(int j = 0; j < Q.get(i).size(); j++) {
                
                //Compute the new normalized K, and T
                int Kj = K - Q.get(i).get(j);
                
                //If the sum of the coefficients of the remaining AMO groups is <= K - Q[i][j],
                // no need to encode any constraint for this group
                if(sum_max_coefs - max_coefs.get(i) < Kj) {
                    continue;
                }
                //If K becomes 0, the encoding is simpler
                else if(Kj == 0) {
                    for(int i2= 0; i2 < Q.size(); i2++) {
                        if(i2!=i) {
                            for(int j2 = 0; j2 < Q.get(i2).size(); j2++) {
                                satModel.addClause(-X.get(i).get(j), -X.get(i2).get(j2));
                            }
                        }
                    }
                    continue;
                }
                
                // Due to the input properties, K cannot become negative
                
                int m = Kj / p2;
                if(Kj%p2 != 0) {
                    m++;
                }
                int T = m*p2 - Kj;
                
                TreeSet<Intpair> usedLits=new TreeSet<>();
                ArrayList<Long> S=new ArrayList<>();
                ArrayList<Long> Shalf=new ArrayList<>();
                
                //For each bucket
                for(int k = 0; k <= p; k++) {
                    //Update input literals util now
                    for(Pair<Integer, TreeSet<Integer>> binputs_p : B_inputs.get(k)) {
                        if(binputs_p.getFirst() != i) {
                            for(Integer l : binputs_p.getSecond()) {
                                usedLits.add(new Intpair(binputs_p.getFirst(), l));
                            }
                        }
                    }
                    
                    ArrayList<Long> U=new ArrayList<>();
                    
                    if(B.get(k).size()>0) {
                        int omittedLeaf = indexesInBuckets.get(k).get(i);
                        if(!(B.get(k).size()==1 && omittedLeaf!=-1)) {
                            addTotalizer(B.get(k),B_inputs.get(k),U, 0, B.get(k).size(), omittedLeaf, constructedTotalizers, satModel);
                        }
                    }
                    
                    if(k==0) {
                        copyArrayList(U, S);
                    }
                    else {
                        // Get the output of the left merger
                        int Tkm1 = T&(1<<(k-1));
                        int firstBit;
                        if(Tkm1!=0) {   //If the bit of T in the previous bucket is 1, shift
                            firstBit=0;
                            resizeArrayList(Shalf, (S.size()+1)/2);
                            usedLits.add(new Intpair(-1,Tkm1)); //If a 1 was considered to get Shalf, this must be added
                        }
                        else {
                            firstBit = 1;
                            resizeArrayList(Shalf, S.size()/2);
                        }
                        
                        for(int l = firstBit; l < S.size(); l+=2) {
                            Shalf.set(l/2, S.get(l));
                        }
                        
                        // Build or reuse the merger
                        ArrayList<Long> it=constructedMergers.get(k-1).get(usedLits);
                        
                        if(it == null) {
                            S.clear();
                            addQuadraticMerge(U,Shalf,S, satModel);
                            ArrayList<Long> Scopy=new ArrayList<Long>(S);
                            constructedMergers.get(k-1).put(usedLits, Scopy);
                        }
                        else {
                            copyArrayList(it, S);
                        }
                    }
                }
                
                //Add the clause forbidding X[i][j] to be true if sum exceeded
                //The last bit never shifts
                satModel.addClause(-X.get(i).get(j), -S.get(m-1));
            }
        }
    }
    
    private static Pair<Long,Long> addTwoComparator(long x1, long x2, boolean leqclauses, boolean geqclauses, Sat satModel) throws IOException {
        long y1 = satModel.createAuxSATVariable();
        long y2 = satModel.createAuxSATVariable();
        
        if(leqclauses) {
            satModel.addClause(-x1, y1);
            satModel.addClause(-x2, y1);
            satModel.addClause(-x1, -x2, y2);
        }
        
        if(geqclauses) {
            satModel.addClause(x1, -y2);
            satModel.addClause(x2, -y2);
            satModel.addClause(x1, x2, -y1);
        }
        
        return new Pair<Long, Long>(y1, y2);
    }
    
    //   Checked 13/3/2021
    private static void addQuadraticMerge(ArrayList<Long> x1, ArrayList<Long> x2, ArrayList<Long> y, Sat satModel) throws IOException {
        if(x1.isEmpty()) {
            copyArrayList(x2, y);
        }
        else if(x2.isEmpty()) {
            copyArrayList(x1, y);
        }
        else {
            resizeArrayList(y, x1.size()+x2.size());
            
            for(int i = 0; i < x1.size() + x2.size(); i++) {
                y.set(i, satModel.createAuxSATVariable());
            }
            for(int i = 0; i < x1.size(); i++) {
                satModel.addClause(-x1.get(i), y.get(i));
                for(int j = 0; j < x2.size(); j++) {
                    satModel.addClause(-x1.get(i), -x2.get(j), y.get(i+j+1));
                }
            }
            for(int i = 0; i < x2.size(); i++) {
                satModel.addClause(-x2.get(i), y.get(i));
            }
        }
    }
    
    //  If odds is true, generate only the odd-numbered outputs, otherwise the even-numbered outputs. 
    private static void addQuadraticMerge2(ArrayList<Long> x1, ArrayList<Long> x2, ArrayList<Long> y, Sat satModel, boolean odds) throws IOException {
        if(x1.isEmpty()) {
            copyArrayList(x2, y);
        }
        else if(x2.isEmpty()) {
            copyArrayList(x1, y);
        }
        else {
            resizeArrayList(y, x1.size()+x2.size());
            
            for(int i = odds?1:0; i < x1.size() + x2.size(); i+=2) {
                y.set(i, satModel.createAuxSATVariable());
            }
            
            // Set the others to true so that the clauses containing them will disappear. 
            for(int i = odds?0:1; i < x1.size() + x2.size(); i+=2) {
                y.set(i, satModel.getTrue());
            }
            
            for(int i = 0; i < x1.size(); i++) {
                satModel.addClause(-x1.get(i), y.get(i));
                for(int j = 0; j < x2.size(); j++) {
                    satModel.addClause(-x1.get(i), -x2.get(j), y.get(i+j+1));
                }
            }
            for(int i = 0; i < x2.size(); i++) {
                satModel.addClause(-x2.get(i), y.get(i));
            }
        }
    }
    
    //  ONly need output sigbit. 
    private static void addQuadraticMergeOne(ArrayList<Long> x1, ArrayList<Long> x2, ArrayList<Long> y, Sat satModel, int sigbit) throws IOException {
        if(x1.isEmpty()) {
            copyArrayList(x2, y);
        }
        else if(x2.isEmpty()) {
            copyArrayList(x1, y);
        }
        else {
            resizeArrayList(y, x1.size()+x2.size());
            
            for(int i = 0; i < sigbit; i++) {
                y.set(i, satModel.getTrue());
            }
            y.set(sigbit, satModel.createAuxSATVariable());
            for(int i = sigbit+1; i < x1.size() + x2.size(); i++) {
                y.set(i, satModel.getTrue());
            }
            
            for(int i = 0; i < x1.size(); i++) {
                satModel.addClause(-x1.get(i), y.get(i));
                for(int j = 0; j < x2.size(); j++) {
                    satModel.addClause(-x1.get(i), -x2.get(j), y.get(i+j+1));
                }
            }
            for(int i = 0; i < x2.size(); i++) {
                satModel.addClause(-x2.get(i), y.get(i));
            }
        }
    }
    
    private static void addMerge(ArrayList<Long> x1, ArrayList<Long> x2, ArrayList<Long> y, boolean leqclauses, boolean geqclauses, Sat satModel) throws IOException {
        int a = x1.size();
        int b = x2.size();
        
        if(a==0 && b==0) {
            y.clear();
            return;
        }
        
        resizeArrayList(y, a+b);
        
        if(a==1 && b==1) {
            Pair<Long, Long> p=addTwoComparator(x1.get(0),x2.get(0),leqclauses,geqclauses,satModel);
            y.set(0, p.getFirst());
            y.set(1, p.getSecond());
        }
        else if(a == 0) {
            copyArrayList(x2, y);
        }
        else if(b == 0) {
            copyArrayList(x1, y);
        }
        else {
            ArrayList<Long> x1even=new ArrayList<Long>();
            ArrayList<Long> x1odd=new ArrayList<Long>();
            ArrayList<Long> x2even=new ArrayList<Long>();
            ArrayList<Long> x2odd=new ArrayList<Long>();
            
            for(int i = 0; i < a-1; i+=2) {
                x1even.add(x1.get(i));
                x1odd.add(x1.get(i+1));
            }
            if(a%2==1) {
                x1even.add(x1.get(a-1));
            }
            
            for(int i = 0; i < b-1; i+=2) {
                x2even.add(x2.get(i));
                x2odd.add(x2.get(i+1));
            }
            if(b%2==1) {
                x2even.add(x2.get(b-1));
            }
            
            ArrayList<Long> zeven = new ArrayList<Long>();
            ArrayList<Long> zodd = new ArrayList<Long>();
            
            addMerge(x1even, x2even,zeven,leqclauses,geqclauses, satModel);
            addMerge(x1odd, x2odd,zodd,leqclauses,geqclauses, satModel);
            
            ArrayList<Long> z=new ArrayList<Long>(a+b);
            for(int i=0; i<a+b; i++) z.add(0L);  //  Initialise z
            
            if(a%2==0) {
                if(b%2==0) {
                    for(int i = 0; i < (a+b)/2; i++) {
                        z.set(2*i, zeven.get(i));
                    }
                    
                    for(int i = 0; i < (a+b)/2; i++) {
                        z.set(2*i + 1, zodd.get(i));
                    }
                    
                    y.set(0, z.get(0));
                    y.set(a+b-1, z.get(a+b-1));
                    for(int i = 1; i < a+b-2; i+=2) {
                        Pair<Long, Long> p = addTwoComparator(z.get(i),z.get(i+1),leqclauses,geqclauses, satModel);
                        y.set(i, p.getFirst());
                        y.set(i+1, p.getSecond());
                    }
                }
                else {
                    for(int i = 0; i < (a+b)/2 + 1; i++) {
                        z.set(2*i, zeven.get(i));
                    }
                    
                    for(int i = 0; i < (a+b)/2; i++) {
                        z.set(2*i + 1, zodd.get(i));
                    }
                    
                    y.set(0, z.get(0));
                    for(int i = 1; i < a+b-1; i+=2) {
                        Pair<Long, Long> p = addTwoComparator(z.get(i),z.get(i+1),leqclauses,geqclauses, satModel);
                        y.set(i, p.getFirst());
                        y.set(i+1, p.getSecond());
                    }
                }
            }
            else { //a%2==1
                if(b%2==0) {
                    addMerge(x2,x1,y,leqclauses,geqclauses,satModel);
                }
                else{
                    for(int i = 0; i < (a+1)/2; i++) {
                        z.set(2*i, zeven.get(i));
                    }
                    for(int i = 0; i < (b+1)/2; i++) {
                        z.set(a + 2*i, zeven.get((a+1)/2 + i));
                    }
                    
                    for(int i = 0; i < a/2; i++) {
                        z.set(2*i+1, zodd.get(i));
                    }
                    for(int i = 0; i < b/2; i++) {
                        z.set(a + 2*i+1, zodd.get(a/2 + i));
                    }
                    
                    y.set(0, z.get(0));
                    y.set(a+b-1, z.get(a+b-1));
                    for(int i = 1; i < a+b-2; i+=2) {
                        Pair<Long, Long> p = addTwoComparator(z.get(i),z.get(i+1),leqclauses,geqclauses, satModel);
                        y.set(i, p.getFirst());
                        y.set(i+1, p.getSecond());
                    }
                }
            }
        }
    }
    
    //  Simple totalizer, used in GPW
    //  Checked 13/3/2021
    private static void addTotalizer(ArrayList<Long> x, ArrayList<Long> y, Sat satModel) throws IOException {
        int n = x.size();
        
        if(n<=1) {
            copyArrayList(x, y);
            return;
        }
        
        ArrayList<ArrayList<Long>> tree = new ArrayList<>(2*n-1);
        for(int i=0; i<2*n-1; i++) {
            tree.add(new ArrayList<Long>());
        }
        
        // Fill leaf nodes with coefficients
        for(int i = 0; i < n; i++) {
            int idx = n-1+i;
            tree.get(idx).add(x.get(i));
        }
        
        for(int i = n-2; i >= 0; i--) {
            int ls = tree.get(lchild(i)).size();
            int rs = tree.get(rchild(i)).size();
            
            assert tree.get(i).size()==0;
            
            for(int j = 0; j < ls + rs; j++) {
                tree.get(i).add(satModel.createAuxSATVariable());
            }
            
            for(int j = 0; j < ls; j++) {
                satModel.addClause(-tree.get(lchild(i)).get(j), tree.get(i).get(j));
                for(int k = 0; k < rs; k++) {
                    satModel.addClause(-tree.get(lchild(i)).get(j), -tree.get(rchild(i)).get(k), tree.get(i).get(j+k+1));
                }
            }
            for(int k = 0; k < rs; k++) {
                satModel.addClause(-tree.get(rchild(i)).get(k), tree.get(i).get(k));
            }
        }
        
        assert tree.get(0).size()==x.size();
        copyArrayList(tree.get(0), y);
    }
    
    private static int lchild(int i) {
        return 2*i+1;
    }
    private static int rchild(int i) {
        return 2*i+2;
    }
    
    //  More complex totalizer used in LPW. 
    //Pre:: omitted node is never alone in x
    //  Checked 14/3/2021
    private static void addTotalizer(ArrayList<Long> x, ArrayList<Pair<Integer, TreeSet<Integer>>> inputBits, ArrayList<Long> y, int lIndex, 
        int partSize, int omittedLeaf,
        HashMap<TreeSet<Intpair>, ArrayList<Long>> constructed, Sat satModel) throws IOException {
        
        y.clear();
        
        //Base case, leaf. Ommitted leaf should never reach a partSize==1
        if(partSize==1) {
            y.add(x.get(lIndex));
        }
        
        //Recursive case, branch in the binary tree
        else {
            //In local encoding (omittedLeaf!=-1), if already constructed, retrieve and return
            //A tree containing an omitted leaf is never reused
            TreeSet<Intpair> input=new TreeSet<Intpair>();
            for(int i = lIndex; i < lIndex+partSize; i++) {
                int group = inputBits.get(i).getFirst();
                if(i!=omittedLeaf) {
                    for(Integer j : inputBits.get(i).getSecond()) {
                        input.add(new Intpair(group,j));
                    }
                }
            }
            
            ArrayList<Long> it = constructed.get(input);
            if(it != null){
                copyArrayList(it, y);
                return;
            }
            
            int lSize = partSize/2;
            int rSize = partSize - partSize/2;
            int rlIndex = lIndex+lSize;
            
            //If left child not present, return right child
            if(lSize==1 && omittedLeaf==lIndex) {
                addTotalizer(x, inputBits, y, rlIndex, rSize,omittedLeaf, constructed, satModel);
                return;
            }
            //If right child not present, return left child
            else if(rSize==1 && omittedLeaf==rlIndex){
                addTotalizer(x, inputBits, y, lIndex, lSize,omittedLeaf, constructed, satModel);
                return;
            }
            
            ArrayList<Long> yleft=new ArrayList<Long>();
            ArrayList<Long> yright=new ArrayList<Long>();
            
            addTotalizer(x, inputBits, yleft, lIndex, lSize, omittedLeaf, constructed, satModel);
            addTotalizer(x, inputBits, yright, rlIndex, rSize, omittedLeaf, constructed, satModel);
            
            if(lIndex <= omittedLeaf && omittedLeaf < lIndex+lSize) {
                lSize--;
            }
            else if(rlIndex <= omittedLeaf && omittedLeaf < rlIndex+rSize) {
                rSize--;
            }
            
            y.clear();
            for(int j = 0; j < lSize + rSize; j++) {
                y.add(satModel.createAuxSATVariable());
            }
            
            for(int j = 0; j < lSize; j++) {
                satModel.addClause(-yleft.get(j), y.get(j));
                for(int k = 0; k < rSize; k++) {
                    satModel.addClause(-yleft.get(j), -yright.get(k), y.get(j+k+1));
                }
            }
            for(int k = 0; k < rSize; k++) {
                satModel.addClause(-yright.get(k), y.get(k));
            }
            
            // Store totalizer
            constructed.put(input, new ArrayList<Long>(y));
        }
    }
    
    private static void addSorting(ArrayList<Long> x, ArrayList<Long> y, boolean leqclauses, boolean geqclauses, Sat satModel) throws IOException {
        //Codifies a mergesort
        int n = x.size();
        
        if(n==0) {
            y.clear();
            return;
        }
        
        if(n==1) {
            copyArrayList(x, y);
        }
        else if(n==2){
            Pair<Long,Long> p=addTwoComparator(x.get(0),x.get(1),leqclauses,geqclauses,satModel);
            y.clear();
            y.add(p.getFirst());
            y.add(p.getSecond());
        }
        else{
            ArrayList<Long> z1=new ArrayList<Long>();
            ArrayList<Long> z2=new ArrayList<Long>();
            
            ArrayList<Long> x1 = new ArrayList<Long>(x.subList(0, n/2));
            ArrayList<Long> x2 = new ArrayList<Long>(x.subList(n/2, n));
            
            addSorting(x1,z1,leqclauses,geqclauses, satModel);
            addSorting(x2,z2,leqclauses,geqclauses, satModel);
            addMerge(z1,z2,y,leqclauses,geqclauses, satModel);
        }
    }
    
    //  k=0 should be most significant bit or least? Must be least.
    private static boolean nthBit(int x, int k) {
        return (((x >>> k) & 1) == 1);
    }
    
    private static int floorlog2(int n){
        if(n <= 0) throw new IllegalArgumentException();
        int log1 = 31 - Integer.numberOfLeadingZeros(n);
        
        int log2 = (int) Math.floor(Math.log(n)/Math.log(2));
        assert log1==log2;
        return log1;
    }
    
    private static int exp2(int n) {
        if(n==0) return 1;
        return 1 << n;
    }
    
    public static <T> void copyArrayList(ArrayList<T> a, ArrayList<T> b) {
        b.clear();
        for(int i=0; i<a.size(); i++) {
            b.add(a.get(i));
        }
    }
    
    private static void resizeArrayList(ArrayList<Long> a, int n) {
        while(a.size()>n) {
            a.remove(a.size()-1);
        }
        while(a.size()<n) {
            a.add(0L);
        }
    }
}
