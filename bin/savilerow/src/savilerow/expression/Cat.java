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

// Concatenate a series of matrices into one normally-indexed matrix. 

public class Cat extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public Cat(ArrayList<ASTNode> a) {
        super(a);
    }
    public Cat(ASTNode[] a) {
        super(a);
    }
    
    public ASTNode copy() {
        return new Cat(getChildrenArray());
    }
    
    public boolean typecheck(SymbolTable st) {
        int dim=1;
        if(numChildren()>0) {
            dim=getChild(0).getDimension();
        }
        if(dim<1) {
            System.out.println("ERROR: Expected 1-dimensional or greater matrix inside concatenate: "+this);
            return false;
        }
        for(int i=0; i<numChildren(); i++) {
            if(! getChild(i).typecheck(st)) return false;
            if(getChild(i).getDimension()!=dim) {
                System.out.println("ERROR: Dimensions of matrices in cat function do not match: "+this);
                return false;
            }
        }
        return true;
    }
    
    public ASTNode simplify()
    {
        // Check everything is a matrix literal
        for(int i=0; i<numChildren(); i++) {
            if( ! (getChild(i) instanceof CompoundMatrix || getChild(i) instanceof EmptyMatrix 
                || (getChild(i) instanceof Identifier && getChild(i).getCategory()==ASTNode.Constant))) {
                return null;
            }
        }
        
        ArrayList<ASTNode> cm=new ArrayList<ASTNode>();
        
        for(int i=0; i<numChildren(); i++) {
            ASTNode inner=getChildConst(i);
            if(getChild(i) == inner) {
                inner.detachChildren();
            }
            cm.addAll(inner.getChildren(1));
        }
        return CompoundMatrix.make(cm);
    }
    
    public int getDimension() {
        if(numChildren()==0) return 1;
        return getChild(0).getDimension();
    }
    public boolean isRelation() {
        //  If any matrix is int then all are cast to int.
        boolean isbool=true;
        for(int i=0; i<numChildren(); i++) {
            if( ! getChild(i).isRelation()) {
                isbool=false;
            }
        }
        return isbool;
    }
    public boolean isNumerical() {
        return !isRelation();
    }
    
    public String toString()
    {
        StringBuilder b=new StringBuilder();
        b.append("cat(");
        for(int i=0; i<numChildren(); i++) {
            b.append(getChild(i));
            if(i<numChildren()-1) b.append(",");
        }
        b.append(")");
        return b.toString();
    }
}
