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


import savilerow.CmdFlags;
import savilerow.model.SymbolTable;

// Two children, the alldiff matrix and the except constant/param/quantifier expression (usually will be 0).

public class AllDifferentExcept extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public AllDifferentExcept(ASTNode r, ASTNode except) {
        super(r, except);
    }
    public boolean typecheck(SymbolTable st) {
        if(!getChild(0).typecheck(st)) return false;
        if(!getChild(1).typecheck(st)) return false;
        if(getChild(0).getDimension()!=1) {
            CmdFlags.println("ERROR: Expected one-dimensional matrix as first argument of allDiffExcept constraint: "+this);
            return false;
        }
        if(getChild(1).getDimension()!=0 || getChild(1).getCategory()>ASTNode.Quantifier ) {
            CmdFlags.println("ERROR: Expected constant, parameter or quantifier expression as second argument of alldifferent_except constraint: "+this);
            return false;
        }
        return true;
    }
    
    public ASTNode simplify() {
        ASTNode matrix=getChildConst(0);
        
        if(matrix instanceof EmptyMatrix) {
            return new BooleanConstant(true);
        }
        if(matrix instanceof CompoundMatrix) {
            if(matrix.numChildren()<=2) {
                return new BooleanConstant(true);
            }
        }
        
        //  Evaluate case where everything is constant. 
        if(getChild(1).isConstant() && matrix instanceof CompoundMatrix && matrix.getCategory()==ASTNode.Constant) {
            long specialval=getChild(1).getValue();
            for(int i=1; i<matrix.numChildren(); i++) {
                ASTNode a=matrix.getChild(i);
                for(int j=i+1; j<matrix.numChildren(); j++) {
                    ASTNode b=matrix.getChild(j);
                    long aval=a.getValue();
                    long bval=b.getValue();
                    if(aval!=specialval && aval==bval) {
                        return new BooleanConstant(false);
                    }
                }
            }
            return new BooleanConstant(true);
        }
        
        return null;
    }
    public ASTNode copy()
    {
        return new AllDifferentExcept(getChild(0), getChild(1));
    }
    
    public boolean isRelation(){return true;}
    public boolean strongProp() {
        return getChild(0).strongProp();   //  In many constraint solvers we will get GAC on alldiff/GCC.
    }
    
    public boolean isChildSymmetric(int childIndex) {
    	return childIndex==0;
    }
    public String toString() {        
        return "alldifferent_except("+getChild(0)+","+getChild(1)+")";
    }
}
