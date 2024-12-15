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

import savilerow.model.Sat;

public class SWC {
    public static void addAMOPBSWC(ArrayList<ArrayList<Integer>> Q, ArrayList<ArrayList<Long>> X, int K, Sat satModel) throws IOException {    
        int N = X.size();
        
        ArrayList<Long> Sin=new ArrayList<Long>();
        ArrayList<Long> Sout=new ArrayList<Long>(K);
        for(int i=0; i<K; i++) Sout.add(0L);
        
        for(int i = 0; i < N; i++){
            Watchdog.copyArrayList(Sout, Sin);
            
            if(i < N-1) {
                for(int j = 0; j < K; j++) {
                    Sout.set(j, satModel.createAuxSATVariable());
                }
            }
            
            if(i < N-1 && i > 0) {
                for(int j = 0; j < K; j++) {
                    satModel.addClause(-Sin.get(j), Sout.get(j));
                }
            }
            
            for(int j = 0; j < X.get(i).size(); j++) {
                int q = Q.get(i).get(j);
                if(i < N-1) {
                    for(int k = 0; k < q; k++) {
                        satModel.addClause(-X.get(i).get(j), Sout.get(k));
                    }
                }
                if(i>0 && i < N-1) {
                    for(int k = 0; k < K-q; k++) {
                        satModel.addClause(-Sin.get(k), -X.get(i).get(j), Sout.get(k+q));
                    }
                }
                if(i>0 && q > 0) {
                    satModel.addClause(-Sin.get(K-q), -X.get(i).get(j));
                }
            }
        }
    }
}