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


import java.io.IOException;
import java.util.ArrayList;

import savilerow.*;
import savilerow.model.Sat;

//  Checked this class 16/3/2021
public class AbioMDDEncoding
{
    public static final long serialVersionUID = 1L;
    
    private Sat satModel;
    
    //Constructor
    public AbioMDDEncoding(Sat _satModel) {
        satModel=_satModel;
    }
    
    //Assert the encoding of 'mdd'	
    public long assertMDD(MDD mdd) throws IOException {
        long[] asserted = new long[mdd.getId()+1];
        
        for(int i = 0; i <= mdd.getId(); i++) {
            asserted[i] = Long.MIN_VALUE;
        }
        return assertMDD(mdd, asserted);
    }
    
    //Asserts an mdd if not already asserted
    private long assertMDD(MDD mdd, long[] asserted) throws IOException {
        if(mdd.isTrueMDD()) {
            return satModel.getTrue();
        }
        else if(mdd.isFalseMDD()) {
            return -satModel.getTrue();
        }
        
        long v=asserted[mdd.getId()];
        if(v==Long.MIN_VALUE) {
            v = satModel.createAuxSATVariable();
            asserted[mdd.getId()] = v;
            
            long velse = assertMDD(mdd.getElseChild(), asserted);
            satModel.addClause(velse, -v);
            if(! CmdFlags.getAuxNonFunctional()) {
                //  Aux SAT variables introduced here must be functionally defined. 
                ArrayList<Long> nosel=new ArrayList<Long>();
                nosel.addAll(mdd.getSelectors());
                nosel.add(-velse);
                nosel.add(v);
                satModel.addClause(nosel);
            }
            
            for(int i = 0; i < mdd.getNSelectors(); i++) {
                Pair<Long, MDD> p = mdd.getSelectorAndChild(i);
                if(p.getSecond() != mdd.getElseChild())
                {
                    long vi = assertMDD(p.getSecond(), asserted);
                    satModel.addClause(vi, -p.getFirst(), -v);
                    if(! CmdFlags.getAuxNonFunctional()) {
                        satModel.addClause(-vi, -p.getFirst(), v);
                    }
                }
            }
        }
        
        return v;
    }
}
