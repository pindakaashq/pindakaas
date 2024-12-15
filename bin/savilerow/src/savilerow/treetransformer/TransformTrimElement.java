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

public class TransformTrimElement extends TreeTransformerTopdown
{
    public TransformTrimElement(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof ElementOne)
        {
            ASTNode mat=curnode.getChildConst(0);
            int numelements=mat.numChildren()-1;
            
            if(mat instanceof CompoundMatrix) {
                Intpair a=curnode.getChild(1).getBounds();
                if(a.lower>1 || a.upper<numelements) {
                    ArrayList<ASTNode> newelements=new ArrayList<>();
                    
                    if(a.lower<1) a.lower=1;
                    if(a.upper>numelements) a.upper=numelements;
                    if(mat==curnode.getChild(0)) {
                        mat.detachChildren();
                    }
                    curnode.getChild(1).setParent(null);
                    for(long i=a.lower; i<=a.upper; i++) {
                        newelements.add(mat.getChild((int)i));
                    }
                    
                    return new NodeReplacement(new ElementOne(CompoundMatrix.make(newelements), BinOp.makeBinOp("-", curnode.getChild(1), NumberConstant.make(a.lower-1))));
                }
            }
        }
        return null;
    }
}
