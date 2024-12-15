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

import savilerow.model.SymbolTable;

// Takes any 1D matrix expression and indexes it, with out-of-bounds indices being 
// mapped to the index value itself. 

public class ElementId extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public ElementId(ASTNode a, ASTNode b) {
        super(a,b);
    }
    
    public ASTNode copy() {
        return new ElementId(getChild(0), getChild(1));
    }
    
    public boolean toFlatten(boolean propagate) {
        return true;
    }
    
    //  Always numerical even if children are boolean. 
    public boolean isNumerical() {
        return true;
    }
    
    public boolean typecheck(SymbolTable st) {
        for(int i=0; i<numChildren(); i++) {
            if(! getChild(i).typecheck(st)) return false;
        }
        
        // Check right number of dimensions.
        if(getChild(0).getDimension() != 1) {
            System.out.println("ERROR: Dimension mismatch in elementId: "+this);
            return false;
        }
        
        if(! (getChild(0).isNumerical() || getChild(0).isRelation())) {
            System.out.println("ERROR: Numerical or boolean matrix required in elementId: "+this);
            return false;
        }
        
        if(! (getChild(1).isNumerical() || getChild(1).isRelation())) {
            System.out.println("ERROR: Numerical index required in elementId: "+this);
            return false;
        }
        
        return true;
    }
    
    @Override
    public ASTNode simplify() {
        ASTNode mat=getChildConst(0);
        if(mat.isMatrixLiteral()) {
            ArrayList<ASTNode> mat_elements=mat.getChildren(1);
            ArrayList<Intpair> mat_index=mat.getIndexDomains().get(0).getIntervalSet();
            
            //  Pad the matrix and turn into MatrixDeref. 
            ArrayList<Intpair> indices=getChild(1).getIntervalSetExp();
            
            if(indices!=null) {
                if(indices.size()==0) {
                    return null;   ///   Something odd has happened
                }
                ArrayList<ASTNode> newmat=new ArrayList<ASTNode>();
                for(int i=0; i<indices.size(); i++) {
                    for(long idx=indices.get(i).lower; idx<=indices.get(i).upper; idx++) {
                        if(Intpair.contains(mat_index, idx)) {
                            long loc = Intpair.location(mat_index, idx);
                            newmat.add(mat_elements.get((int)loc));
                        }
                        else {
                            newmat.add(NumberConstant.make(idx));
                        }
                    }
                }
                
                return new MatrixDeref(
                    CompoundMatrix.make(Intpair.makeDomain(indices, false), newmat, false), 
                    getChild(1));
            }
        }
        return null;
    }
    
    public Intpair getBounds() {
        //  Assume max or min can be any element from the matrix, or any element from the index set. 
        Intpair a=getChild(0).getBounds();
        Intpair b=getChild(1).getBounds();
        return a.union(b);
    }
    public ArrayList<Intpair> getIntervalSetExp() {
        //  Same assumption as above. 
        return Intpair.union(getChild(0).getIntervalSetExp(), getChild(1).getIntervalSetExp());
    }
    
    public String toString() {
        return "elementId("+getChild(0)+","+getChild(1)+")";
    }
}
