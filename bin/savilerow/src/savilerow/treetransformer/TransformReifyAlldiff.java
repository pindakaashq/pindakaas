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

import savilerow.expression.*;
import savilerow.model.Model;

//  Get rid of reify(alldiff()) because Gecode/Chuffed don't have it.

public class TransformReifyAlldiff extends TreeTransformerBottomUpNoWrapper
{
    public TransformReifyAlldiff(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof AllDifferent && curnode.getParent()!=null && !(curnode.getParent().inTopAnd()))
        {
            ASTNode cm=curnode.getChildConst(0);
            
            if(cm.numChildren()>3) {
                // reified alldiff
                // Replace with pairwise decomposition.
                ArrayList<ASTNode> conjunction=new ArrayList<ASTNode>();
                for(int i=1; i<cm.numChildren(); i++) {
                    for(int j=i+1; j<cm.numChildren(); j++) {
                        conjunction.add(new AllDifferent(cm.getChild(i), cm.getChild(j)));
                    }
                }
                
                return new NodeReplacement(new And(conjunction));
            }
        }
        return null;
    }
}

