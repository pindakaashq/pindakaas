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
//  Transform the occurrence constraints atleast and atmost 
//  for Minion output.

import savilerow.expression.*;

public class TransformOccurrence extends TreeTransformerBottomUpNoWrapper
{
    public TransformOccurrence() {
        super(null);
    }
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if((curnode instanceof AtMost || curnode instanceof AtLeast) && !(curnode.getParent() instanceof Tag))
        {
            ASTNode values=curnode.getChildConst(2);
            ASTNode occs=curnode.getChildConst(1);
            
            if(values instanceof CompoundMatrix && occs instanceof CompoundMatrix)
            {
                // Transform into multiple atmost/atleast constraints -- to go to occurrenceleq/geq in Minion. 
                ArrayList<ASTNode> new_cons=new ArrayList<ASTNode>();
                for(int i=1; i<values.numChildren(); i++)   // From 1 now because of CompoundMatrix index domain
                {
                    ArrayList<ASTNode> newoccs=new ArrayList<ASTNode>();
                    newoccs.add(occs.getChild(i));
                    ArrayList<ASTNode> newvals=new ArrayList<ASTNode>();
                    newvals.add(values.getChild(i));
                    
                    if(curnode instanceof AtMost) {
                        new_cons.add(new Tag(new AtMost(curnode.getChild(0), CompoundMatrix.make(newoccs), CompoundMatrix.make(newvals))));
                    }
                    else
                    {
                        new_cons.add(new Tag(new AtLeast(curnode.getChild(0), CompoundMatrix.make(newoccs), CompoundMatrix.make(newvals))));
                    }
                }
                return new NodeReplacement(new And(new_cons));
            }
        }
        return null;
    }
}

