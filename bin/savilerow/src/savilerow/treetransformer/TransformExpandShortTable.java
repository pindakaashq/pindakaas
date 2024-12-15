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

//  Turn all tableshort into table by expanding the table of short supports into a conventional table. 

public class TransformExpandShortTable extends TreeTransformerBottomUpNoWrapper
{
    public TransformExpandShortTable(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof TableShort) {
	        ASTNode shortsups=curnode.getChildConst(1);
            
            //  Matrices are not allowed to be empty -- these cases should have simplified to true or false.  
            assert curnode.getChild(0) instanceof CompoundMatrix && shortsups instanceof CompoundMatrix;
            
            // Construct a comprehension that will unroll into the table. 
            
            ArrayList<ASTNode> vars = curnode.getChild(0).getChildren(1);
            
            ArrayList<ASTNode> compvarnames=new ArrayList<ASTNode>();
            ArrayList<ASTNode> compforalls = new ArrayList<ASTNode>();
            
            for(int i=0; i<vars.size(); i++) {
                // Make a new comprehension id, with a name used nowhere else.
                ASTNode id=new Identifier(m, m.global_symbols.newAuxId());
                ASTNode dom=m.global_symbols.getDomain(vars.get(i).toString());
                compforalls.add(new ComprehensionForall(id, dom));
                compvarnames.add(id);
            }
            
            //  Copy of the tableshort constraint with the comprehension variables. 
            ASTNode newshorttab=new TableShort(m, CompoundMatrix.make(compvarnames), curnode.getChild(1));
            
            ASTNode comp=new ComprehensionMatrix(CompoundMatrix.make(compvarnames), compforalls, newshorttab);
            
            // Now make a table containing the comprehension, using the scope from the original shorttable constraint.
            ASTNode tab=new Table(m, curnode.getChild(0), comp);
            
            // Unroll the comprehension.
            TransformQuantifiedExpression tqe=new TransformQuantifiedExpression(m);
            tab=tqe.transform(tab);
            
            return new NodeReplacement(tab);
        }
        return null;
    }
    
}

