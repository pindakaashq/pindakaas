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
import java.util.HashMap;
import java.util.HashSet;

import savilerow.expression.*;
import savilerow.model.Model;

//  Truncate lex-ordering constraints when a pair is different via alldiff, lessthan.

public class TransformLexAlldiff extends TreeTransformerBottomUpNoWrapper
{
    public TransformLexAlldiff(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof And && curnode.getParent() instanceof Top)
        {
            // If this conjunction contains any lex constraints, then construct the diffs datastructure and filter all lex cts with it.
            boolean haslex=false;
            for(int i=0; i<curnode.numChildren(); i++) {
                ASTNode a=curnode.getChild(i);
                if(a instanceof LexLess || a instanceof LexLessEqual) {
                    haslex=true;
                    break;
                }
            }
            
            if(!haslex) {
                return null;
            }
            
            ArrayList<HashSet<ASTNode>> diffs=new ArrayList<HashSet<ASTNode>>();
            HashMap<ASTNode, ArrayList<Integer>> astToDiffs=new HashMap<ASTNode, ArrayList<Integer>>();
            
            for(int i=0; i<curnode.numChildren(); i++) {
                if(curnode.getChild(i) instanceof AllDifferent && curnode.getChild(i).getChild(0) instanceof CompoundMatrix) {
                    int idx=diffs.size();
                    ArrayList<ASTNode> ch=curnode.getChild(i).getChild(0).getChildren(1);
                    diffs.add(new HashSet<ASTNode>(ch));
                    for(int j=0; j<ch.size(); j++) {
                        if(!astToDiffs.containsKey(ch.get(j))) {
                            astToDiffs.put(ch.get(j), new ArrayList<Integer>());
                        }
                        astToDiffs.get(ch.get(j)).add(idx);
                    }
                }
                else if(curnode.getChild(i) instanceof Less) {
                    int idx=diffs.size();
                    ArrayList<ASTNode> ch=curnode.getChild(i).getChildren();
                    diffs.add(new HashSet<ASTNode>(ch));
                    for(int j=0; j<ch.size(); j++) {
                        if(!astToDiffs.containsKey(ch.get(j))) {
                            astToDiffs.put(ch.get(j), new ArrayList<Integer>());
                        }
                        astToDiffs.get(ch.get(j)).add(idx);
                    }
                }
            }
            
            if(diffs.size()==0) {
                return null;
            }
            
            for(int i=0; i<curnode.numChildren(); i++) {
                ASTNode a=curnode.getChild(i);
                if( (a instanceof LexLess || a instanceof LexLessEqual) && a.getChild(0) instanceof CompoundMatrix && a.getChild(1) instanceof CompoundMatrix) {
                    jloop:
                    for(int j=1; j<a.getChild(0).numChildren(); j++) {
                        // Look up the alldiffs containing element j of the first matrix.
                        ArrayList<Integer> checkdiffs=astToDiffs.get(a.getChild(0).getChild(j));
                        if(checkdiffs!=null) {
                            for(int k=0; k<checkdiffs.size(); k++) {
                                if(diffs.get(checkdiffs.get(k)).contains(a.getChild(1).getChild(j))) {
                                    // Pair j is different so the constraint can be replaced with one truncated at j.
                                    
                                    ArrayList<ASTNode> left=new ArrayList<ASTNode>(a.getChild(0).getChildren().subList(1, j+1));
                                    ArrayList<ASTNode> right=new ArrayList<ASTNode>(a.getChild(1).getChildren().subList(1, j+1));
                                    
                                    //  Make a strict less constraint because the two vectors cannot be equal at j.
                                    ASTNode ct=new LexLess(CompoundMatrix.make(left), CompoundMatrix.make(right));
                                    
                                    curnode.setChild(i, ct);
                                    
                                    break jloop;
                                }
                            }
                        }
                    }
                    
                }
            }
        }
        return null;
    }
}

