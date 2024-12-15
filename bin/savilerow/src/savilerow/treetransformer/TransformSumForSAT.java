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

public class TransformSumForSAT extends TreeTransformerBottomUpNoWrapper
{
    public TransformSumForSAT() { super(null); }
    protected NodeReplacement processNode(ASTNode curnode)
	{
        if(curnode instanceof ToVariable && curnode.getChild(0) instanceof WeightedSum && !curnode.getChild(1).isConstant())
        {
            return new NodeReplacement(new ToVariable(BinOp.makeBinOp("-", curnode.getChild(0), curnode.getChild(1)), NumberConstant.make(0)));
        }
        if(curnode instanceof Less && curnode.getChild(0) instanceof WeightedSum && !curnode.getChild(1).isConstant())
        {
            return new NodeReplacement(new Less(BinOp.makeBinOp("-", curnode.getChild(0), curnode.getChild(1)), NumberConstant.make(0)));
        }
        if(curnode instanceof LessEqual && curnode.getChild(0) instanceof WeightedSum && !curnode.getChild(1).isConstant())
        {
            return new NodeReplacement(new LessEqual(BinOp.makeBinOp("-", curnode.getChild(0), curnode.getChild(1)), NumberConstant.make(0)));
        }
        if(curnode instanceof Less && curnode.getChild(1) instanceof WeightedSum && !curnode.getChild(0).isConstant())
        {
            return new NodeReplacement(new Less(NumberConstant.make(0), BinOp.makeBinOp("-", curnode.getChild(1), curnode.getChild(0))));
        }
        if(curnode instanceof LessEqual && curnode.getChild(1) instanceof WeightedSum && !curnode.getChild(0).isConstant())
        {
            return new NodeReplacement(new LessEqual(NumberConstant.make(0), BinOp.makeBinOp("-", curnode.getChild(1), curnode.getChild(0))));
        }
        if(curnode instanceof Equals && curnode.getChild(0) instanceof WeightedSum && !curnode.getChild(1).isConstant())
        {
            return new NodeReplacement(new Equals(BinOp.makeBinOp("-", curnode.getChild(0), curnode.getChild(1)), NumberConstant.make(0)));
        }
        if(curnode instanceof Equals && curnode.getChild(1) instanceof WeightedSum && !curnode.getChild(0).isConstant())
        {
            return new NodeReplacement(new Equals(NumberConstant.make(0), BinOp.makeBinOp("-", curnode.getChild(1), curnode.getChild(0))));
        }
        
        return null;
    }
}

