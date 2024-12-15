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




import savilerow.expression.ASTNode;

public class ReplaceASTNode extends TreeTransformerBottomUpNoWrapper
{
    // For each node, if it is equal to id
    // then replace it. 
    ASTNode id;
    ASTNode replacement;
    
    // This one runs forever if replacement contains id.
    
    public ReplaceASTNode(ASTNode i, ASTNode rep)
    {
        super(null);
        assert ! rep.contains(i);
        id=i;
        replacement=rep;
    }
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    // Check hashcode first -- might make it faster because the hash code is cached.
	    if(curnode.hashCode()==id.hashCode() && curnode.equals(id))
	    {
	        return new NodeReplacement(replacement.copy());
	    }
	    return null;
	}
}

