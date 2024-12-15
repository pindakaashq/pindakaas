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

// Magic function that turns a 1-d matrix into a list of arguments for its containing function/operator.
// It relies on being inside ONLY MatrixDeref, SafeMatrixDeref, MatrixSlice.

public class Unpack extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public Unpack(ASTNode numitems, ASTNode a) {
        super(numitems, a);
    }
    
    public ASTNode copy() {
        return new Unpack(getChild(0), getChild(1));
    }
    
    // To be called by simplifier above.
    public ArrayList<ASTNode> items() {
        if(getChild(1) instanceof CompoundMatrix || getChild(1) instanceof EmptyMatrix) {
            long nitems=getChild(0).getValue();
            assert nitems==getChild(1).numChildren()-1;
            ArrayList<ASTNode> tmp=getChild(1).getChildren(1);
            return tmp;
        }
        return null;
    }
    public Intpair getBounds() {
	    return new Intpair(Long.MIN_VALUE, Long.MAX_VALUE);
	}
	public PairASTNode getBoundsAST() {
	    return new PairASTNode(new NegInfinity(), new PosInfinity());
	}
    
    public boolean toFlatten(boolean propagate) {return false;}
    
	public String toString()
	{
	    return "unpack("+getChild(0)+","+getChild(1)+")";
	}
}