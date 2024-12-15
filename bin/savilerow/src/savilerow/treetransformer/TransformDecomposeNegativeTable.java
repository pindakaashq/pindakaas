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

//  Get rid of negative table because Gecode doesn't have it.

public class TransformDecomposeNegativeTable extends TreeTransformerBottomUpNoWrapper
{
    public TransformDecomposeNegativeTable(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof NegativeTable)
        {
            ASTNode table=curnode.getChildConst(1);
            
            ArrayList<ASTNode> and=new ArrayList<ASTNode>();
            
            for(int i=1; i<table.numChildren(); i++) {
                ArrayList<ASTNode> orlist=new ArrayList<ASTNode>();
                
                for(int j=1; j<curnode.getChild(0).numChildren(); j++) {
                    orlist.add(new AllDifferent(curnode.getChild(0).getChild(j), table.getChild(i).getChild(j)));
                }
                
                and.add(new Or(orlist));
            }
            return new NodeReplacement(new And(and));
        }
        return null;
    }
}

