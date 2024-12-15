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

//  Little experiment -- turn flattened product cts to tables. 

public class TransformProductToTable extends TreeTransformerBottomUp
{
    public TransformProductToTable(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof ToVariable && curnode.getChild(0) instanceof Times)
        {
            // get the variables
            ArrayList<ASTNode> vars=curnode.getChild(0).getChildren();
            vars.add(curnode.getChild(1));
            
            ArrayList<ASTNode> varquants=new ArrayList<ASTNode>();
            
            for(int i=0; i<vars.size(); i++) {
                if(vars.indexOf(vars.get(i))==i) {
                    varquants.add(new ComprehensionForall(vars.get(i), m.global_symbols.getDomain(vars.get(i).toString())));
                }
            }
            
            // Vars has three elements.
            ASTNode table=new ComprehensionMatrix(new CompoundMatrix(vars), varquants, curnode.copy());   // Curnode becomes the condition for accepting a tuple. 
            // A little black magic here: the comprehension variables shadow the decision variables in curnode.
            
            ASTNode tablect=new Table(m, new CompoundMatrix(vars), table);
            
            System.out.println(tablect);
            
            TransformQuantifiedExpression tqe=new TransformQuantifiedExpression(m);
            tablect=tqe.transform(tablect);
            
            System.out.println(tablect);
            
            return new NodeReplacement(tablect);
        }
        return null;
    }
}

