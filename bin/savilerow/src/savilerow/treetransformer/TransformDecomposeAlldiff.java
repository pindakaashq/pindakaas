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

// Very simple decompose alldiff into binary not-equals for testing. 

public class TransformDecomposeAlldiff extends TreeTransformerBottomUpNoWrapper
{
    public TransformDecomposeAlldiff(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof AllDifferent && curnode.getChild(0) instanceof CompoundMatrix && curnode.getChild(0).numChildren()>3)
        {
            ArrayList<ASTNode> decomp=new ArrayList<ASTNode>();
            
            for(int i=1; i<curnode.getChild(0).numChildren()-1; i++) {
                for(int j=i+1; j<curnode.getChild(0).numChildren(); j++) {
                    ArrayList<ASTNode> tmp=new ArrayList<ASTNode>();
                    tmp.add(curnode.getChild(0).getChild(i));
                    tmp.add(curnode.getChild(0).getChild(j));
                    decomp.add(new AllDifferent(new CompoundMatrix(tmp)));
                }
            }
            return new NodeReplacement(new And(decomp));
        }
        return null;
    }
    
}

