package savilerow.mdd;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Jordi Coll
    
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

public class AMOPBMDDBuilder extends MDDBuilder
{
    public static final long serialVersionUID = 1L;
    
    ArrayList<ArrayList<MDD>> L_MDDs;
	ArrayList<ArrayList<R_M>> L;
	int K;	
	ArrayList<ArrayList<Integer>> Q;
	ArrayList<ArrayList<Long>> X;
	
	public AMOPBMDDBuilder(ArrayList<ArrayList<Integer>> _Q, ArrayList<ArrayList<Long>> _X, int _K, boolean _longedges) {
        Q=_Q;
        X=_X;
        K=_K;
        
        longedges=_longedges;
        
        for(int i = 0; i < Q.size(); i++) {
            sortCoefsDecreasing(Q.get(i), X.get(i));
        }
        
        depth = Q.size()+1;
        initL();
        
        L_MDDs=new ArrayList<ArrayList<MDD>>(Q.size());
        for(int i=0; i<Q.size(); i++) {
            L_MDDs.add(new ArrayList<MDD>());
        }
    }
    
    //  copied from util.
    //  Checked 16/3/2021
    public static void sortCoefsDecreasing(ArrayList<Integer> _Q, ArrayList<Long> _X) {
        int length = _Q.size();
        
        for (int i = 0; i < length; ++i) {
            boolean swapped = false;
            for (int j = 0; j < length - (i+1); j++)
            {
                if (_Q.get(j) < _Q.get(j+1)) {
                    Integer tmp_Q = _Q.get(j+1);
                    _Q.set(j+1, _Q.get(j));
                    _Q.set(j, tmp_Q);
                    
                    Long tmp_X = _X.get(j+1);
                    _X.set(j+1, _X.get(j));
                    _X.set(j, tmp_X);
                    
                    swapped = true;
                }
            }
            if (!swapped) break;
        }
    }
    
    public void buildMDD() {
        root=MDDConstruction(0,K).mdd;
    }
    
    private int inf_sum(int possible_inf, int x) {
      if(possible_inf == Integer.MAX_VALUE) {
          return Integer.MAX_VALUE;
      }
      else if(possible_inf == Integer.MIN_VALUE) {
          return Integer.MIN_VALUE;
      }
      else return possible_inf + x;
    }
    
    
    //Insert ordered with respect to the intervals [B,Y].
    //The ArrayList 'layer' is order, so we can use dicotomic search
    // Precondition: rm_in doesnt exists in layer
    // Checked 16/3/2021
    private void insertMDD(R_M rm_in, int i_l) {
        R_M act;
        
        ArrayList<R_M> layer=L.get(i_l);
        
        if(layer.isEmpty()){
           layer.add(rm_in);
           return;
        }
        int n=layer.size();
        int i=0;
        int min=0;
        int max=n-1;
        
        i=(max-min)/2;
        
        while(min<max) {
            act=layer.get(i);
            if(act.B>rm_in.Y) {
                max=i-1;
            }
            else { //if(act->Y<rm_in->B) { //otherwise
                min=i+1;
            }
            i=min+(max-min)/2;
        }
        
        act=layer.get(i); // min=max=i
        
        if(act.B>rm_in.Y){
            //i==i;
        } else { //if(act.Y<rm_in.B) { //otherwise
            i++;
        }
        L.get(i_l).add(i, rm_in);
    }
    
    // Checked 16/3/2021
    private R_M searchMDD(int i_k, int i_l) {
        ArrayList<R_M> layer = L.get(i_l);
        
        R_M res = new R_M();
        R_M act = new R_M();
        res.mdd = null;
        int n=layer.size();
        int i=0;
        int min=0;
        int max=0;
        boolean trobat=false;
        
        if(n>0) {
            max=n-1;
            
            i=(max-min)/2;
            while(min<=max && !trobat) {
                act=layer.get(i);
                if(i_k>=act.B && i_k<=act.Y) {
                    res=act;
                    trobat=true;
                }
                else if(act.B>i_k){
                    max=i-1;
                }
                else { //if(act.Y<i_k) { //otherwise
                    min=i+1;
                }
                i=min+(max-min)/2;
            }
        }
        return res;
    }
    
    // Checked 16/3/2021
    private R_M MDDConstruction(int i_l, int i_k) {
        R_M rm_cert;
        R_M rm_fals;
        R_M rm_new;
        MDD mdd_new=null;
        
        rm_new=searchMDD(i_k, i_l);
        
        if(rm_new.mdd==null) {
            ArrayList<R_M> rmdds = new ArrayList<R_M>();
            ArrayList<MDD> mdds = new ArrayList<MDD>();
            int maxB = Integer.MIN_VALUE;
            int minY = Integer.MAX_VALUE;
            boolean allequal = true;
            MDD m = null;
            
            for(int i = 0; i < Q.get(i_l).size(); i++) {
                int i_a=Q.get(i_l).get(i);
                R_M rm = MDDConstruction(i_l+1, i_k-i_a);
                rmdds.add(rm);
                mdds.add(rm.mdd);
                if(m==null) {
                    m = rm.mdd;
                }
                else {
                    allequal = allequal && m==rm.mdd;
                }
                
                if(inf_sum(rm.B, i_a) > maxB) maxB = inf_sum(rm.B, i_a);
                if(inf_sum(rm.Y, i_a) < minY) minY = inf_sum(rm.Y, i_a);
            }
            
            //Else case, same as coefficient 0
            R_M rm = MDDConstruction(i_l+1, i_k);
            rmdds.add(rm);
            mdds.add(rm.mdd);
            allequal = allequal && m==rm.mdd;
            
            if(rm.B > maxB) maxB = rm.B;
            if(rm.Y < minY) minY = rm.Y;
            
            boolean reusechild = longedges && allequal;
            
            if(reusechild) {
                rm_new=new R_M();
                rm_new.mdd=mdds.get(0);
                rm_new.B=maxB;
                rm_new.Y=rmdds.get(0).Y;
            }
            else {
                mdd_new=new MDD(nodeCount++, X.size() - i_l);
                for(int i = 0; i < mdds.size()-1; i++) {
                    mdd_new.addChild(X.get(i_l).get(i), mdds.get(i));
                }
                mdd_new.setElseChild(mdds.get(mdds.size()-1));
                L_MDDs.get(i_l).add(mdd_new);
                rm_new=new R_M(mdd_new, maxB, minY);
                insertMDD(rm_new, i_l);
            }
        }
        return rm_new;
    }
    
    // sum(Q) <= k
    //  Checked 16/3/2021
    private void initL() {
        ArrayList<Integer> sums_max=new ArrayList<Integer>(depth);
        for(int i=0; i<depth; i++) {
            sums_max.add(0);
        }
        
        L = new ArrayList<ArrayList<R_M>>(depth);
        for(int i=0; i<depth; i++) {
            L.add(new ArrayList<R_M>());
        }
        
        R_M rm_fals;
        R_M rm_cert;
        
        sums_max.set(depth-1, 0); // for the leaves
        for(int i=depth-2; i>= 0; i--) {
            sums_max.set(i, sums_max.get(i+1) + Collections.max(Q.get(i)));
        }
        
        rm_fals=new R_M();
        rm_fals.mdd=MDD.MDDFalse();
        rm_fals.B=Integer.MIN_VALUE;
        rm_fals.Y=-1;
        
        if(longedges) {
            for(int i=0; i<depth-1; i++) {
                L.get(i).add(rm_fals);
                rm_cert=new R_M();
                rm_cert.mdd=MDD.MDDTrue();
                rm_cert.B=sums_max.get(i);
                rm_cert.Y=Integer.MAX_VALUE;
                L.get(i).add(rm_cert);
            }
        }
        
        rm_cert=new R_M();
        rm_cert.mdd=MDD.MDDTrue();
        rm_cert.B=0;
        rm_cert.Y=Integer.MAX_VALUE;
        L.get(depth-1).add(rm_fals);
        L.get(depth-1).add(rm_cert);
    }
}
