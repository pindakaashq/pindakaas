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


import java.util.ArrayList;

// This class is for use in the parser only -- once the shunting-yard algorithm
// has been run, there should be no occurrences of this remaining.

public class Expression extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    // The children are [Part, BinOpPlaceholder, Part ...]
    
    public Expression(ArrayList<ASTNode> e) {
        super(e);
    }
    
	public ASTNode copy()
	{
	    return new Expression(getChildren());
	}
}
