package savilerow.expression;
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


// Tag wraps an ASTNode to mark it.
// Used in transform passes to avoid transforming the same term twice. 
// The tag deletes itself in the next simplify pass. 

public class Tag extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public Tag(ASTNode in)
    {
        super(in);
    }
    
	public ASTNode copy()
	{
	    return new Tag(getChild(0));
	}
	
	public ASTNode simplify() {
	    getChild(0).setParent(null);
	    return getChild(0);
	}
	
	@Override
	public int getDimension() {
	    return getChild(0).getDimension();
	}
	
	public boolean isRelation() {
	    return getChild(0).isRelation();
	}
	public boolean strongProp() {
        return getChild(0).strongProp();
    }
	public boolean isNumerical() {
	    return getChild(0).isNumerical();
	}
	
	public Intpair getBounds() {
	    return getChild(0).getBounds();
	}
	public long getValue() {
	    return getChild(0).getValue();
	}
}
