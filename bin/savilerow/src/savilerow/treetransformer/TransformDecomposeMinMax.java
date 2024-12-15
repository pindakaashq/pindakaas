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

// Very simple decomposition of lex constraints -- would benefit from AC-CSE to
// factor out the conjunctions of disequality constraints.

public class TransformDecomposeMinMax extends TreeTransformerBottomUpNoWrapper
{
    public TransformDecomposeMinMax(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    // Decompose Min and Max constraints for SAT output. 
        if(curnode instanceof ToVariable && 
            (curnode.getChild(0) instanceof Min || curnode.getChild(0) instanceof Max)) {
            ArrayList<ASTNode> ch=curnode.getChild(0).getChildren();
            
            ArrayList<ASTNode> newcts=new ArrayList<ASTNode>();
            
            if(curnode.getChild(0) instanceof Min) {
                for(int i=0; i<ch.size(); i++) {
                    newcts.add(new LessEqual(curnode.getChild(1), ch.get(i)));
                }
            }
            else {
                for(int i=0; i<ch.size(); i++) {
                    newcts.add(new LessEqual(ch.get(i), curnode.getChild(1)));
                }
            }
            
            // For both min and max, the result var is equal to one of the vars in the min or max function.
            
            ArrayList<ASTNode> or=new ArrayList<ASTNode>();
            for(int i=0; i<ch.size(); i++) {
                or.add(new Equals(ch.get(i), curnode.getChild(1)));
            }
            newcts.add(new Or(or));
            
            return new NodeReplacement(new And(newcts));
        }
        return null;
    }
    
}

