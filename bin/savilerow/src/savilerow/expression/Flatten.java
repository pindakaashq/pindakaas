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

import savilerow.model.SymbolTable;

// Flatten a matrix to a one-dimensional matrix.

public class Flatten extends Unary
{
    public static final long serialVersionUID = 1L;
    public Flatten(ASTNode a) {
        super(a);
    }
    
    public ASTNode copy()
    {
        return new Flatten(getChild(0));
    }
    
    public boolean typecheck(SymbolTable st) {
        if(! getChild(0).typecheck(st)) return false;
        if(getChild(0).getDimension()<1) {
            System.out.println("ERROR: Expected matrix inside flatten function: "+this);
            return false;
        }
        return true;
	}
    
    public ASTNode simplify()
    {
        // Flatten is idempotent
        if(getChild(0) instanceof Flatten) {
            getChild(0).setParent(null);
            return getChild(0);
        }
        
        ASTNode mat=getChildConst(0);
        
        if(mat instanceof EmptyMatrix) {
            // Flatten of an empty matrix is a similar empty matrix with one empty dimension, and same base domain.  
            ArrayList<ASTNode> idxdoms=new ArrayList<ASTNode>();
            idxdoms.add(new IntegerDomain(new EmptyRange()));
            return new EmptyMatrix(new MatrixDomain(mat.getChild(0).getChild(0), idxdoms));
        }
        
        if(mat instanceof CompoundMatrix && canFlatten(mat)) {
            ArrayList<ASTNode> entries=new ArrayList<ASTNode>();
            
            flatten_compound_matrix(entries, mat, mat==getChild(0));
            
            return CompoundMatrix.make(entries);
        }
        return null;
    }
    
    //  Depth-first traversal to collect all entries in the matrix.
    //  currentLevelSetParent may be true at the top level, once it becomes false
    //  it must be false everywhere below. 
    private void flatten_compound_matrix(ArrayList<ASTNode> entries, ASTNode mat, boolean levelAboveDetach) {
        assert mat instanceof CompoundMatrix;
        
        for(int i=1; i<mat.numChildren(); i++) {
            ASTNode child=mat.getChildConst(i);
            boolean canDetach=(child==mat.getChild(i)) && levelAboveDetach;
            
            if(child instanceof CompoundMatrix) {
                flatten_compound_matrix(entries, child, canDetach);
            }
            else if(child instanceof EmptyMatrix) {
                // Drop it.
            }
            else {
                if(canDetach) {
                    child.setParent(null);
                }
                entries.add(child);
            }
        }
    }
    
    private boolean canFlatten(ASTNode mat) {
        assert mat instanceof CompoundMatrix;
        
        for(int i=1; i<mat.numChildren(); i++) {
            ASTNode child=mat.getChildConst(i);
            
            if(child instanceof CompoundMatrix) {
                boolean child_flat=canFlatten(child);
                if(!child_flat) {
                    return false;
                }
            }
            else if(child instanceof EmptyMatrix) {
                // Drop it.
            }
            else {
                if(child.getDimension()>0) {
                    return false;
                }
            }
        }
        return true;
    }
    
    public Intpair getBounds() {
	    return getChild(0).getBounds();
	}
	public ArrayList<Intpair> getIntervalSetExp() {
	    return getChild(0).getIntervalSetExp();
	}
    
    public boolean toFlatten(boolean propagate) {return false;}
    
    public boolean isRelation() {
        return getChild(0).isRelation();
    }
    public boolean isNumerical() {
        return getChild(0).isNumerical();
    }
    
    public int getDimension() {
        return 1;
    }
    
    public ArrayList<ASTNode> getIndexDomains() {
        // Find the index domain sizes of the inner matrix.
        
        ArrayList<ASTNode> idxdoms=getChild(0).getIndexDomains();
        if(idxdoms==null) {
            return null;
        }
        
        long numelements=1L;
        
        for(int i=0; i<idxdoms.size(); i++) {
            ArrayList<Intpair> ranges=idxdoms.get(i).getIntervalSet();
            long rangeitems=0;
            for(int j=0; j<ranges.size(); j++) {
                if(! (ranges.get(j).isEmpty())) rangeitems+=ranges.get(j).upper-ranges.get(j).lower+1L;
            }
            numelements=numelements*rangeitems;
        }
        
        idxdoms.clear();
        idxdoms.add(new IntegerDomain(new Range(NumberConstant.make(1), NumberConstant.make(numelements))));
        
	    return idxdoms;
	}
    
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
	    // Minion implicitly flattens.
	    assert !bool_context;
	    getChild(0).toMinion(b, false);
	}
	public String toString()
	{
	    return "flatten("+getChild(0)+")";
	}
}
