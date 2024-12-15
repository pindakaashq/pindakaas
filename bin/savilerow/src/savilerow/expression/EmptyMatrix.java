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
import java.util.ArrayList;

// This is needed so that an empty matrix can have a dimension and type (int or bool)

public class EmptyMatrix extends ASTNodeC
{ 
    public static final long serialVersionUID = 1L;
    // Child 0 is a matrix domain.  this allows us to store the number of dimensions and 
    // the base type in a way that is consistent with other places.  
    
    public EmptyMatrix(ASTNode type) {
        super(type);
        assert type instanceof MatrixDomain;
    }
    
    public boolean isRelation() {
        // Check the base domain. 
        return getChild(0).getChild(0).isBooleanSet();
    }
    
    public boolean isNumerical() {
        return ! (getChild(0).getChild(0).isBooleanSet());
    }
    
    public ASTNode copy() {
	    return new EmptyMatrix(getChild(0));
	}
	
	public boolean toFlatten(boolean propagate) { return false; }
	
	// Use the bounds of the base domain.
	public Intpair getBounds() {
	    return getChild(0).getChild(0).getBounds();
	}
	
	// Just get dimension of the matrix domain. 
	public int getDimension() {
	    return getChild(0).numChildren()-3;
	}
	
	@Override
	public boolean isRegularMatrix() {
	    return true;
	}
	
	@Override public boolean isMatrixLiteral() {
	    return true;
	}
	
	public ArrayList<ASTNode> getIndexDomains() {
	    return getChild(0).getChildren(3);  // skip first three children.
	}
	
	public ArrayList<ASTNode> getIndexDomainsIrregular() {
	    return getChild(0).getChildren(3);  // skip first three children.
	}
	
	public boolean isTuple() {
	    return getDimension()==1;
	}
	public int getTupleLength() {
        return 0;
    }
    
	// Put into the normal form where the outermost dimension of an EmptyMatrix must be empty.
	@Override
	public ASTNode simplify() {
	    ASTNode firstidx=getChild(0).getChild(3);
	    if(firstidx.getCategory()==ASTNode.Constant && firstidx.getIntervalSet().size()>0) {
	        // rewrite
	        
	        ArrayList<ASTNode> inneridx=getChild(0).getChildren(4);  // Delete the first idx.
	        
	        ArrayList<Intpair> ranges=firstidx.getIntervalSet();
	        ArrayList<ASTNode> cm=list();
	        for(int i=0; i<ranges.size(); i++) {
	            Intpair p=ranges.get(i);
	            for(long j=p.lower; j<=p.upper; j++) {
	                cm.add(new EmptyMatrix(new MatrixDomain(getChild(0).getChild(0), inneridx)));
	            }
	        }
	        return new CompoundMatrix(firstidx, cm);
	    }
	    return null;
	}
	
	// ALL output methods except E' drop the dimension and base type. 
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
        b.append("[]");
	}
	
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("[]");
	}
	
	public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("[]");
	}
	
	public String toString() {
	    return "([] : `"+getChild(0)+"`)";
	}
}
