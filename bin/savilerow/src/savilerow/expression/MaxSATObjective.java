package savilerow.expression;
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

import savilerow.model.Sat;

public class MaxSATObjective extends ASTNodeC {
    public static final long serialVersionUID = 1L;
  /* ====================================================================
     constructor()
     ==================================================================== */
    public MaxSATObjective(ArrayList<ASTNode> inList) {
        super(inList);
    }
    public MaxSATObjective(ASTNode[] inList) {
        super(inList);
    }
    
    public ASTNode copy() {
        return new MaxSATObjective(getChildrenArray());
    }
    
    public void toSAT(Sat satModel) throws IOException {
        //  Encode each term separately
        if(getParent() instanceof Maximising) {
            for(int i=0; i<numChildren(); i++) {
                ArrayList<Intpair> a=getChild(i).getIntervalSetExp();
                long small=(a.size()>0)? a.get(0).lower : 0;
                for(int j=0; j<a.size(); j++) {
                    for(long val=a.get(j).lower; val<=a.get(j).upper; val++) {
                        if(val>small) {
                            //  Skip smallest value, encode others as a gain vs smallest value.
                            satModel.addSoftClause(getChild(i).directEncode(satModel, val), val-small);
                        }
                    }
                }
            }
        }
        else {
            assert getParent() instanceof Minimising;
            
            for(int i=0; i<numChildren(); i++) {
                ArrayList<Intpair> a=getChild(i).getIntervalSetExp();
                long large=(a.size()>0)? a.get(a.size()-1).upper : 0;
                for(int j=0; j<a.size(); j++) {
                    for(long val=a.get(j).lower; val<=a.get(j).upper; val++) {
                        if(val<large) {
                            //  Skip largest value, encode others as a gain relative to largest value. 
                            satModel.addSoftClause(getChild(i).directEncode(satModel, val), large-val);
                        }
                    }
                }
            }
        }
    }
    
    @Override
    public int polarity(int child) {
        return polarity();
    }
}