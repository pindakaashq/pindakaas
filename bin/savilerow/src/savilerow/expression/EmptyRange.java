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

// A ClosedRange can simplify to an EmptyRange .. 

public class EmptyRange extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public EmptyRange() {
        super();
    }
    
    public ASTNode copy() {
	    return new EmptyRange();
	}
	
	public ArrayList<Intpair> getIntervalSet() {
	    return new ArrayList<Intpair>();
	}
	
	public Intpair getBounds() {
	    return new Intpair(1, 0);
	}
	public PairASTNode getBoundsAST() {
	    return new PairASTNode(NumberConstant.make(1), NumberConstant.make(0));
	}
	
	public String toString() {
	    return "";
	}
	
	public boolean containsValue(long val) {
	    return false;
	}
	
	public boolean toFlatten(boolean propagate) {return false;}
}
