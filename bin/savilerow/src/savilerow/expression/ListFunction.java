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

// Accepts any number of arguments -- produces a list by flattening each and 
// concatenating all in the given order. 

public class ListFunction extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public ListFunction(ArrayList<ASTNode> a) {
        super(a);
    }
    public ListFunction(ASTNode[] a) {
        super(a);
    }
    
    public ASTNode copy() {
        return new ListFunction(getChildrenArray());
    }
    
    public boolean typecheck(SymbolTable st) {
        for(int i=0; i<numChildren(); i++) {
            if(! getChild(i).typecheck(st)) return false;
            if(! (getChild(i).isRelation() || getChild(i).isNumerical())) {
                System.out.println("ERROR: list function argument is not integer or Boolean: "+this);
                return false;
            }
        }
        return true;
    }
    
    public ASTNode simplify()
    {
        // Rewrite to a Cat
        ArrayList<ASTNode> cm=new ArrayList<ASTNode>();
        
        for(int i=0; i<numChildren(); i++) {
            ASTNode inner=getChildConst(i);
            int dim=inner.getDimension();
            if(dim>1) {
                cm.add(new Flatten(inner));
            }
            else if(dim<1) {
                //  Wrap in a list. 
                cm.add(CompoundMatrix.make(inner));
            }
            else {
                cm.add(inner);
            }
        }
        return new Cat(cm);
    }
    
    public int getDimension() {
        return 1;
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
        b.append("list(");
        for(int i=0; i<numChildren(); i++) {
            b.append(getChild(i));
            if(i<numChildren()-1) b.append(",");
        }
        b.append(")");
        return b.toString();
    }
}
