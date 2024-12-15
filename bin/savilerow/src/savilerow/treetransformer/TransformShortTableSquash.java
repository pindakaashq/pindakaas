package savilerow.treetransformer;
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





import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;

import savilerow.TupleCompress;
import savilerow.expression.*;
import savilerow.model.Model;

//  Turn all tableshort into table by expanding the table of short supports into a conventional table.

public class TransformShortTableSquash extends TransformTableToShortTable
{
    public TransformShortTableSquash(Model _m) { super(_m); }


    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof TableShort) {
            ASTNode tuples=curnode.getChildConst(1);
            
            //  Matrices are not allowed to be empty -- these cases should have simplified to true or false.
            assert curnode.getChild(0) instanceof CompoundMatrix && tuples instanceof CompoundMatrix;
            ArrayList<ASTNode> vars = curnode.getChild(0).getChildren(1);
            
            ArrayList<ArrayList<Intpair>> doms = getDomainLists(vars, m);
            
            ASTNode compressed=compressShortTab(tuples, doms);
            
            if(compressed==null) {
                return null;
            }
            else {
                return new NodeReplacement(new TableShort(m, CompoundMatrix.make(vars), compressed));
            }
        }
        return null;
    }
    
    public static ASTNode compressShortTab(ASTNode tuples, ArrayList<ArrayList<Intpair>> doms) {
        
        //System.out.println(vars + "::" + doms);

        HashSet<ArrayList<Long>> long_tuples = new HashSet<ArrayList<Long>>();

        for(int i = 1; i < tuples.numChildren(); i++) {
          ArrayList<Long> tup;
          tup = new ArrayList<Long>(Collections.nCopies(doms.size(), TupleCompress.free_value));

          ASTNode child = tuples.getChild(i);
          for(int j = 1; j < child.getChildren().size(); ++j) {
            long var = child.getChild(j).getChild(1).getValue();
            long val = child.getChild(j).getChild(2).getValue();
            tup.set((int)var-1, val);
          }
          long_tuples.add(tup);
        }
        //System.out.println(long_tuples);
        HashSet<ArrayList<Long>> shorttups;
        shorttups = TupleCompress.full_squeeze_short_tuples(long_tuples, doms, false);
 
        if(shorttups.size() < long_tuples.size()) {
            return convertHashSet(shorttups);
        }
        else {
            return null;
        }
    }
}
