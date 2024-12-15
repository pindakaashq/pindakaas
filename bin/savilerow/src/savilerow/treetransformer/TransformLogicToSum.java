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





import savilerow.expression.*;

public class TransformLogicToSum extends TreeTransformerBottomUpNoWrapper
{
    public TransformLogicToSum() {
        super(null);
    }
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if( (curnode instanceof And || curnode instanceof Or) && !(curnode.getParent() instanceof Top) )
        {
            ASTNode sum=new WeightedSum(curnode.getChildren());
            
            if(curnode instanceof And) {
                return new NodeReplacement(new LessEqual(NumberConstant.make(curnode.numChildren()), sum));
            }
            else {
                return new NodeReplacement(new LessEqual(NumberConstant.make(1), sum));
            }
        }
        return null;
    }
}

