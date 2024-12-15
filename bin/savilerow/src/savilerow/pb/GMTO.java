package savilerow.pb;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2020 Jordi Coll, Peter Nightingale
    
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

public class GMTO {
    
    public static void addAMOPBModuloTotalizer(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int K, Sat satModel) throws IOException {
        //Compute vector of moduli
        ArrayList<Integer> moduli=new ArrayList<Integer>();
        baseSelectionMTO(Q,K,moduli);
        
        //Fill tree with variables and add clauses
        ArrayList<HashMap<Integer, Long>> D = new ArrayList<>(moduli.size()+1);
        for(int i=0; i<moduli.size()+1; i++) {
            D.add(new HashMap<Integer, Long>());
        }
        nLevelsMTO(Q,X,0,Q.size(),moduli,D, satModel);
        
        //Ensure sum(Q*X <= k)
        comtMTO(K,moduli,D,null, satModel);
    }
    
    private static void baseSelectionMTO(ArrayList<ArrayList<Integer>> Q, int K, ArrayList<Integer> moduli) {
        assert moduli.isEmpty();
        moduli.clear();
        
        ArrayList<Integer> q=new ArrayList<Integer>();
        for(ArrayList<Integer> v : Q) {
            q.addAll(v);
        }
        
        int k = K;
        while(k>1) {
            int bestCandidate=-1;
            int bestCandidateVotes=0;
            
            for(int candidate = k; candidate >= 2; candidate--) {
                int candidateVotes = 0;
                for(int x : q) {
                    if(x!=0 && x%candidate == 0){
                        candidateVotes++;
                        if(candidateVotes>bestCandidateVotes) {
                            bestCandidate = candidate;
                            bestCandidateVotes=Integer.MAX_VALUE;
                        }
                    }
                }
                if(bestCandidate==candidate) {
                    bestCandidateVotes=candidateVotes;
                }
            }
            
            //For inner nodes in case of very large K w.r.t. coefficient values
            if(bestCandidate==-1) {
                bestCandidate=2;
            }
            
            for(int i=0; i<q.size(); i++) {
                q.set(i, q.get(i)/bestCandidate);
            }
            
            moduli.add(bestCandidate);
            k/=bestCandidate;
        }
	}
	
	
    private static void nLevelsMTO(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int lIndex, int partSize, 
        ArrayList<Integer> moduli, ArrayList< HashMap<Integer, Long> > D, Sat satModel) throws IOException {
        int n = moduli.size(); //Number of modulo
        int m = partSize; //Number of variables
        
        //Base case, leaf
        if(m==1) {
            int modProd = 1;
            for(int mo : moduli) {
                modProd*=mo;
            }
            
            ArrayList<Integer> w = new ArrayList<Integer>(Q.get(lIndex));
            for(int i = n; i >= 0; i--) {
                D.get(i).put(0, satModel.getTrue());
                
                HashMap<Integer, Boolean> varWithCoefCreated = new HashMap<>();
                
                for(int j = 0; j < w.size(); j++) {
                    int wmod = w.get(j)/modProd;
                    
                    if(wmod!=0) {
                        if(D.get(i).get(wmod)==null) {
                            D.get(i).put(wmod, X.get(lIndex).get(j)); //Initialize with the original variable itself
                            varWithCoefCreated.put(wmod, false);
                        }
                        else {
                            if(!varWithCoefCreated.get(wmod)) { //Replace original variable by a half-reified aux variable
                                long v = satModel.createAuxSATVariable();
                                satModel.addClause(-D.get(i).get(wmod), v);
                                D.get(i).put(wmod, v);
                                varWithCoefCreated.put(wmod, true);
                            }
                            satModel.addClause(-X.get(lIndex).get(j), D.get(i).get(wmod));
                        }
                    }
                }
                
                if(i > 0) {
                    for(int j = 0; j < w.size(); j++) {
                        w.set(j, w.get(j)%modProd);
                    }
                    modProd/=moduli.get(i-1);
                }
            }
        }
        
        // Recursive case, branch in the binary tree
        else {
            ArrayList<HashMap<Integer, Long>> Dleft=new ArrayList<>(n+1);
            ArrayList<HashMap<Integer, Long>> Dright=new ArrayList<>(n+1);
            for(int i=0; i<n+1; i++) {
                Dleft.add(new HashMap<Integer, Long>());
                Dright.add(new HashMap<Integer, Long>());
            }
            
            int lSize = m/2;
            int rSize = m - m/2;
            nLevelsMTO(Q,X,lIndex, lSize, moduli,  Dleft, satModel);
            nLevelsMTO(Q,X,lIndex+lSize, rSize, moduli, Dright, satModel);
            
            
            ArrayList<Long> c=new ArrayList<Long>(n);
            for(int i=0; i<n; i++) c.add(0L);
            
            
            boolean thisLevelHasCarry = false;
            boolean prevLevelHasCarry;
            for(int h = 0; h < n; h++) {
                prevLevelHasCarry = thisLevelHasCarry;
                thisLevelHasCarry = false;
                D.get(h).put(0, satModel.getTrue());
                c.set(h, satModel.createAuxSATVariable());
                
                for(Map.Entry<Integer,Long> i : Dleft.get(h).entrySet()) {
                    for(Map.Entry<Integer, Long> j : Dright.get(h).entrySet()) {
                        int wi = i.getKey();
                        long xi = i.getValue();
                        
                        int wj = j.getKey();
                        long xj = j.getValue();
                        
                        int sum = wi + wj;
                        
                        ArrayList<Long> base = new ArrayList<>(); // Children in a LHS of a implication, unless 0 that are omitted
                        if(wi>0) {
                            base.add(-xi);
                        }
                        if(wj>0) {
                            base.add(-xj);
                        }
                        
                        if(sum>0) { // Clauses for sum==0 trivially satisfied
                            // Clauses for lowest and intermediate digits
                            if(sum<moduli.get(h)) {
                                ArrayList<Long> cl=new ArrayList<>(base); // copy base
                                cl.add(MTOVar(D.get(h), sum, satModel));
                                cl.add(c.get(h));
                                satModel.addClause(cl);
                            }
                            else {
                                thisLevelHasCarry=true;
                                ArrayList<Long> cl=new ArrayList<>(base); // copy base
                                cl.add(c.get(h));
                                satModel.addClause(cl);
                                if(sum > moduli.get(h) && sum%moduli.get(h)>0) {
                                    ArrayList<Long> cl2=new ArrayList<>(base); // copy base
                                    cl2.add(MTOVar(D.get(h),sum%moduli.get(h), satModel));
                                    satModel.addClause(cl2);
                                }
                            }
                        }
                        
                        
                        //Clauses only for intermediate digits
                        if(h>0 && prevLevelHasCarry){ //If previous level never has carry, clauses trivially satisfied
                            sum++; //Last carry added, sum will not be 0
                            if(sum < moduli.get(h)) {
                                ArrayList<Long> cl=new ArrayList<>(base); // copy base
                                cl.add(-c.get(h-1));
                                cl.add(MTOVar(D.get(h),sum, satModel));
                                cl.add(c.get(h));
                                satModel.addClause(cl);
                            }
                            else {
                                thisLevelHasCarry=true;
                                ArrayList<Long> cl=new ArrayList<>(base); // copy base
                                cl.add(-c.get(h-1));
                                cl.add(c.get(h));
                                satModel.addClause(cl);
                                if(sum > moduli.get(h) && sum%moduli.get(h)>0) {
                                    ArrayList<Long> cl2=new ArrayList<>(base); // copy base
                                    cl2.add(-c.get(h-1));
                                    cl2.add(MTOVar(D.get(h), sum%moduli.get(h), satModel));
                                    satModel.addClause(cl2);
                                }
                            }
                        }
                    }
                }
                if(!thisLevelHasCarry) {
                    satModel.addClause(-c.get(h));
                }
            }
            
            prevLevelHasCarry = thisLevelHasCarry;
            
            //Clauses of the uppermost digits
            D.get(n).put(0, satModel.getTrue());
            
            for(Map.Entry<Integer, Long> i : Dleft.get(n).entrySet()) {
                for(Map.Entry<Integer, Long> j : Dright.get(n).entrySet()) {
                    int wi = i.getKey();
                    long xi = i.getValue();
                    
                    int wj = j.getKey();
                    long xj = j.getValue();
                    
                    int sum = wi + wj; 
                    
                    ArrayList<Long> base=new ArrayList<>(); //Children in a LHS of a implication, unless 0 that are ommitted
                    if(wi>0)
                        base.add(-xi);
                    if(wj>0)
                        base.add(-xj);
                    
                    if(sum!=0) {
                        ArrayList<Long> cl=new ArrayList<Long>(base);  // copy base
                        cl.add(MTOVar(D.get(n),sum, satModel));
                        satModel.addClause(cl);
                    }
                    
                    if(prevLevelHasCarry) {
                        ArrayList<Long> cl=new ArrayList<Long>(base);  // copy base
                        cl.add(-c.get(n-1));
                        cl.add(MTOVar(D.get(n),sum+1, satModel));
                        satModel.addClause(cl);
                    }
                }
            }
        }
    
    }
	
    private static long MTOVar(HashMap<Integer,Long> m, int w, Sat satModel) {
        if(!m.containsKey(w)) {
            long x = satModel.createAuxSATVariable();
            m.put(w,x);
            return x;
        }
        else {
            return m.get(w);
        }
    }
    
    private static void comtMTO(int K, ArrayList<Integer> moduli, ArrayList<HashMap<Integer, Long>> D, Long localLit, Sat satModel) throws IOException {
        
        int n = moduli.size();
        ArrayList<Integer> k=new ArrayList<>(n+1);
        for(int i=0; i<n+1; i++) k.add(0);
        
        int modProd = 1;
        for(int lambda : moduli) {
            modProd*=lambda;
        }
        
        for(int i = n; i >=0; i--) {
            k.set(i, K / modProd);
            K%=modProd;
            if(i>0) {
                modProd/=moduli.get(i-1);
            }
        }
        
        ArrayList<Long> c=new ArrayList<>();
        if(localLit != null) {
            c.add(-localLit);
        }
        
        for(int i = n; i >= 0; i--) {
            if(i<n && k.get(i+1)!=0) {
                if(! D.get(i+1).containsKey(k.get(i+1))) {
                    break; // If not possible to be equal in this level, no need to look at the following levels
                }
                else {
                    c.add(-D.get(i+1).get(k.get(i+1)));
                }
            }
            for(Map.Entry<Integer, Long> p : D.get(i).entrySet()) {
                if(p.getKey() > k.get(i)) {
                    ArrayList<Long> cl=new ArrayList<Long>(c); // copy c
                    cl.add(-p.getValue());
                    satModel.addClause(cl);
                }
            }
        }
    }
    
}
