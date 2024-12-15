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
import java.util.HashSet;

import savilerow.*;
import savilerow.expression.*;
import savilerow.model.Model;

//  Turn all tableshort into table by expanding the table of short supports into a conventional table.

public class TransformTableToShortTable extends TreeTransformerBottomUpNoWrapper
{
    public TransformTableToShortTable(Model _m) { super(_m); }

    public static ArrayList<ArrayList<Intpair>> getDomainLists(ArrayList<ASTNode> varlist, Model m) {
        ArrayList<ArrayList<Intpair>> vardoms = new ArrayList<ArrayList<Intpair>>();
        for(int i=0; i<varlist.size(); i++) {
            ArrayList<Intpair> targetdom;
            if(varlist.get(i) instanceof Identifier) {
                targetdom=m.global_symbols.getDomain(varlist.get(i).toString()).getIntervalSet();
            }
            else {
                targetdom=new ArrayList<Intpair>();
                targetdom.add(varlist.get(i).getBounds());
            }
            vardoms.add(targetdom);
        }
        return vardoms;
    }

    // Return null if there is an empty short support
    // (so the constraint is just true)
    public static ASTNode convertHashSet(HashSet<ArrayList<Long>> shorttups) 
    {
        // turn short tuples into correct structure
        ArrayList<ASTNode> shorttuplist = new ArrayList<ASTNode>();
        for(ArrayList<Long> tup : shorttups) {
          ArrayList<ASTNode> stup = new ArrayList<ASTNode>();
          for(int i = 0; i < tup.size(); ++i) {
            if(tup.get(i) != TupleCompress.free_value) {
              ArrayList<ASTNode> pair = new ArrayList<ASTNode>(2);
              pair.add(NumberConstant.make(i+1));
              pair.add(NumberConstant.make(tup.get(i)));
              stup.add(new CompoundMatrix(pair));
            }
          }
          if(stup.isEmpty()) {
            return CompoundMatrix.make(CompoundMatrix.make(new ArrayList<ASTNode>()));
          }
          shorttuplist.add(new CompoundMatrix(stup));
        }
        return CompoundMatrix.make(shorttuplist);
    }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof Table) {
            ASTNode tuples=curnode.getChildConst(1);
            
            //  Matrices are not allowed to be empty -- these cases should have simplified to true or false.
            assert curnode.getChild(0) instanceof CompoundMatrix && tuples instanceof CompoundMatrix;
            
            // Construct a comprehension that will unroll into the table.
            
            ArrayList<ASTNode> vars = curnode.getChild(0).getChildren(1);
            
            ArrayList<ArrayList<Intpair>> doms = getDomainLists(vars, m);
            
            HashSet<ArrayList<Long>> long_tuples = new HashSet<ArrayList<Long>>();
            
            for(int i = 1; i < tuples.numChildren(); i++) {
              ArrayList<Long> tup = new ArrayList<Long>();
              for(int j = 1; j <= vars.size(); ++j) {
                tup.add(tuples.getChild(i).getChild(j).getValue());
              }
              long_tuples.add(tup);
            }
            
            HashSet<ArrayList<Long>> shorttups;
            shorttups = TupleCompress.full_squeeze_tuples(long_tuples, doms, false);
            if(CmdFlags.verbose_make_short) {
              System.out.println("Squashed a long table. " + long_tuples.size() + " -> " + shorttups.size());
            }
            
            ASTNode tup = convertHashSet(shorttups);
            if(tup == null) {
              if(CmdFlags.verbose_make_short) {
                System.out.println("Table is just 'true'!");
              }
              return new NodeReplacement(new BooleanConstant(true));
            }
            return new NodeReplacement(new TableShort(m, new CompoundMatrix(vars), tup));
        }
        return null;
    }

}
