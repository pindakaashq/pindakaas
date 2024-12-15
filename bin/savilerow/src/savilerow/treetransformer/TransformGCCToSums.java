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
//  Transform GCC into sums/equals 

import savilerow.expression.*;

public class TransformGCCToSums extends TreeTransformerBottomUpNoWrapper
{
    public TransformGCCToSums() {
        super(null);
    }
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof GlobalCard)
        {
            ASTNode target=curnode.getChildConst(0);
            ASTNode vals=curnode.getChildConst(1);
            ASTNode occs=curnode.getChildConst(2);
            
            assert target instanceof CompoundMatrix;
            assert vals instanceof CompoundMatrix;   // Values
            assert occs instanceof CompoundMatrix;   // Cardinality variables/constants
            
            ArrayList<ASTNode> sums=new ArrayList<ASTNode>();
            
            for(int i=1; i<vals.numChildren(); i++) {
                ASTNode value=vals.getChild(i);
                
                ArrayList<ASTNode> newsum=new ArrayList<ASTNode>(target.numChildren()-1);
                
                for(int j=1; j<target.numChildren(); j++) {
                    newsum.add(new Equals(target.getChild(j), value));
                }
                
                ASTNode sum=new WeightedSum(newsum);
                
                sums.add(new Equals(sum, occs.getChild(i)));
            }
            return new NodeReplacement(new And(sums));
            
        }
        return null;
    }
}

