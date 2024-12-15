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

public class AuditTreeLinks extends TreeTransformerTopdown
{
    // For each child, check that it's parent and child number is set appropriately.
    public AuditTreeLinks() { super(null); }
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    for(int i=0; i<curnode.numChildren(); i++) {
	        ASTNode child=curnode.getChild(i);
	        if(child == null) {
	            System.out.println("Null child.");
	            System.out.println(curnode);
	            assert false;
	        }
	        
	        if(child.getParent() != curnode)
	        {
	            System.out.println("Found child with incorrect parent.");
	            System.out.println("Child:"+child);
	            System.out.println("Real Parent:"+curnode);
	            System.out.println("Found Parent:"+child.getParent());
	            assert false;
	        }
	        if(child.getChildNo() != i)
	        {
	            System.out.println("Found child with incorrect child number.");
	            System.out.println("Child:"+child);
	            System.out.println("Real Parent:"+curnode);
	            assert false;
	        }
	    }
	    return null;
	}
}
