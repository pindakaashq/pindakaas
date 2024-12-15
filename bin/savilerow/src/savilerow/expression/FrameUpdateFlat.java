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


import java.io.BufferedWriter;
import java.io.IOException;

// Frame Update constraint.
 
//  frameUpdateFlat(source, target, sourceIndices, targetIndices, blocksize)


public class FrameUpdateFlat extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public FrameUpdateFlat(ASTNode a, ASTNode b, ASTNode c, ASTNode d, ASTNode e) {
        super(new ASTNode[]{a, b, c, d, e});
    }

    public ASTNode copy() {
        return new FrameUpdateFlat(getChild(0), getChild(1), getChild(2), getChild(3), getChild(4));
    }
    
    public boolean isRelation() { return true; }
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    assert bool_context;
	    b.append("frameupdate(");
	    getChild(0).toMinion(b, false);
	    b.append(",");
	    getChild(1).toMinion(b, false);
	    b.append(",");
	    getChild(2).toMinion(b, false);
	    b.append(",");
	    getChild(3).toMinion(b, false);
	    b.append(",");
	    getChild(4).toMinion(b, false);
	    b.append(")");
	}
    
    public String toString() {
        return "frameUpdateFlat(" + getChild(0) + "," + getChild(1) + "," + getChild(2) + "," + getChild(3) + "," + getChild(4) + ")";
    }
}
