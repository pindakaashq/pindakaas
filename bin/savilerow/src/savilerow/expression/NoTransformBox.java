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

public class NoTransformBox extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    // Contains one ASTNode. MUST NOT BE TRANSFORMED BY ANY OF THE 
    // TRANSFORMATION RULES. 
    // This is used to box an expression before running the tree transformer on it. 
    
    public NoTransformBox(ASTNode a)
    {
        super(a);
    }
    
    public ASTNode copy()
	{
	    return new NoTransformBox(getChild(0));
	}
	public boolean toFlatten(boolean propagate) { return false; }
	public boolean isRelation() { return false; }
}
