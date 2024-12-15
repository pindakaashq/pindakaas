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

import savilerow.TabulationUtils;
import savilerow.expression.*;
import savilerow.model.Model;

//  Chuffed is missing division with mixed signs, tabulate in that case. 

public class TransformDivToTable extends TreeTransformerBottomUpNoWrapper
{
    public TransformDivToTable(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof ToVariable && (curnode.getChild(0) instanceof Divide || curnode.getChild(0) instanceof SafeDivide)) {
	        Intpair b1=curnode.getChild(1).getBounds();
	        Intpair b2=curnode.getChild(0).getChild(0).getBounds();
	        Intpair b3=curnode.getChild(0).getChild(1).getBounds();
	        if((b1.lower<0 && b1.upper>0) || (b2.lower<0 && b2.upper>0) || (b3.lower<0 && b3.upper>0)) {
	            TabulationUtils tu=new TabulationUtils(m);
	            return new NodeReplacement(tu.makeTableLong(curnode));
	        }
        }
        return null;
    }
}

