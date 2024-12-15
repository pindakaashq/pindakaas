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

public class ReplaceASTNode2 extends TreeTransformerBottomUpNoWrapper
{
    // For each node, if it is equal to id
    // then replace it. 
    ASTNode id;
    ASTNode replacement;
    
    // Don't replace anything that is inside a Tag, directly or transitively.
    // This is for the case where replacement contains id.
    
    public ReplaceASTNode2(ASTNode i, ASTNode rep)
    {
        super(null);
        id=i;
        replacement=new Tag(rep);
    }
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    boolean intag=false;
	    ASTNode par=curnode;
	    while(par !=null ) {
	        if(par instanceof Tag) { intag=true; break; }
	        par=par.getParent();
	    }
	    
	    if(curnode.equals(id) && !intag)
	    {
	        return new NodeReplacement(replacement.copy());
	    }
	    return null;
	}
}

