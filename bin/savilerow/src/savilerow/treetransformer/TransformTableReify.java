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

import savilerow.TabulationUtils;
import savilerow.expression.*;
import savilerow.model.Model;

//  For solvers that have no reified table constraint, turn it into a table. 

public class TransformTableReify extends TreeTransformerBottomUpNoWrapper
{
    public TransformTableReify(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
    {
        if(curnode instanceof ToVariable && curnode.getChild(0) instanceof Table) {
            ASTNode tab=curnode.getChild(0).getChildConst(1);
            ArrayList<ASTNode> scope=curnode.getChild(0).getChild(0).getChildren(1);
            
            ArrayList<ArrayList<Intpair>> domains=new ArrayList<>();
            for(int i=0; i<scope.size(); i++) {
                domains.add(scope.get(i).getIntervalSetExp());
            }
            
            ArrayList<ASTNode> newtab=new ArrayList<>();
            
            //  Make a hash table of the tuples of the original table constraint.
            HashSet<ArrayList<Long>> tabhash=new HashSet<>();
            
            for(int i=1; i<tab.numChildren(); i++) {
                ArrayList<Long> tmp = new ArrayList<Long>();
                for(int j=1; j<=tab.getChild(i).getTupleLength(); j++) {
                    tmp.add(tab.getChild(i).getValueIdx(j));
                }
                tabhash.add(tmp);
            }
            
            ArrayList<ASTNode> repltab=new ArrayList<>();
            
            ArrayList<Long> tup=new ArrayList<>();
            
            enumerateTuples(0, domains, repltab, tabhash, tup);
            
            scope.add(curnode.getChild(1));  // Extend the scope to include the reification expression. 
            
            return new NodeReplacement(new Table(m, CompoundMatrix.make(scope), CompoundMatrix.make(repltab)));
        }
        return null;
    }
    
    private void enumerateTuples(int depth, ArrayList<ArrayList<Intpair>> domains, ArrayList<ASTNode> newtab, HashSet<ArrayList<Long>> tabhash, ArrayList<Long> tup) {
        if(depth<domains.size()) {
            ArrayList<Intpair> dom=domains.get(depth);
            for(int i=0; i<dom.size(); i++) {
                for(long val=dom.get(i).lower; val<=dom.get(i).upper; val++) {
                    tup.add(val);
                    
                    enumerateTuples(depth+1, domains, newtab, tabhash, tup);
                    
                    tup.remove(tup.size()-1);
                }
            }
        }
        else {
            assert depth==domains.size();
            
            boolean inset=tabhash.contains(tup);
            
            tup.add(inset?1L:0L);  //  Add the value for the reification variable.
            
            newtab.add(TabulationUtils.makeTableTuple(tup));  // Make the appropriate CompoundMatrix type. 
            
            tup.remove(tup.size()-1);
        }
    }
}
