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

public class Count extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    
    public Count(ASTNode mat, ASTNode val) {
        super(mat,val);
    }
    
    public ASTNode copy() {
        return new Count(getChild(0), getChild(1));
    }
    
    public boolean strongProp() {
        return getChild(0).strongProp();    //  Strong iff the elements of the matrix have strong propagation
    }
    public boolean isNumerical() {
        return true;
    }
    public boolean isSet() {
        return false;
    }
    
    public boolean toFlatten(boolean propagate) {
        return true; 
    }
    
    public Intpair getBounds()
    {
        if(getChild(0) instanceof CompoundMatrix) {
            return new Intpair(0, getChild(0).numChildren()-1);
        }
        else {
            return new Intpair(0, Long.MAX_VALUE);
        }
    }
    public PairASTNode getBoundsAST() {
        return new PairASTNode(NumberConstant.make(0), new Length(getChild(0)));
    }
    
    @Override
    public ASTNode simplify() {
        ASTNode mat=getChildConst(0);
        
        if(mat instanceof EmptyMatrix) {
            return NumberConstant.make(0);
        }
        if(mat instanceof CompoundMatrix && getChild(1).isConstant()) {
            long value=getChild(1).getValue();
            boolean allconstant=true;
            long counter=0; // how many are equal to value.
            
            ArrayList<ASTNode> ls=new ArrayList<ASTNode>();
            
            for(int i=1; i<mat.numChildren(); i++) {
                ASTNode element=mat.getChild(i);
                if(element.isConstant()) {
                    if(element.getValue()==value) {
                        // Must keep this entry
                        ls.add(element);
                        counter++;
                    }
                    // else can drop this entry.
                }
                else {
                    allconstant=false;
                    ls.add(element);
                }
            }
            
            if(allconstant) {
                return NumberConstant.make(counter);
            }
            if(ls.size()<(mat.numChildren()-1)) {
                // The matrix had some constants that are != value in it, these have been filtered out.
                if(mat==getChild(0)) {
                    for(int i=0; i<ls.size(); i++) ls.get(i).setParent(null);  //  Do not copy.
                }
                return new Count(CompoundMatrix.make(ls), getChild(1));
            }
        }
        return null;
    }
    
    public ASTNode normalise() {
        // sort by hashcode
        if (!(getChild(0) instanceof CompoundMatrix)) {
            return this;
        }
        
        ArrayList<ASTNode> ch = getChild(0).getChildren(1);
        
        boolean changed = sortByHashcode(ch);
        if (changed) {
            for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
            getChild(1).setParent(null);
            return new Count(new CompoundMatrix(ch), getChild(1));
        }
        else {
            return this;
        }
    }
    
    public ASTNode normaliseAlpha() {
        // sort by name
        if (!(getChild(0) instanceof CompoundMatrix)) {
            return null;
        }
        
        ArrayList<ASTNode> ch = getChild(0).getChildren(1);
        
        boolean changed = sortByAlpha(ch);
        if (changed) {
            for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
            getChild(1).setParent(null);
            return new Count(new CompoundMatrix(ch), getChild(1));
        }
        else {
            return null;
        }
    }
    
    public boolean typecheck(SymbolTable st) {
        for(int i=0; i<numChildren(); i++) {
            if(! getChild(i).typecheck(st)) return false;
        }
        
        // Check dimensions
        if(getChild(0).getDimension() != 1) {
            System.out.println("ERROR: Count function must contain 1-dimensional matrix: "+this);
            return false;
        }
        if(getChild(1).getDimension() != 0) {
            System.out.println("ERROR: Found matrix, expected single expression in second argument of Count function: "+this);
            return false;
        }
        return true;
    }
    
    public void toMinionWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException
    {
        b.append("occurrence(");
        getChild(0).toMinion(b, false);
        b.append(",");
        getChild(1).toMinion(b, false);
        b.append(",");
        aux.toMinion(b, false);
        b.append(")");
    }
    
    public void toFlatzincWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException
    {
        b.append("constraint count(");
        getChild(0).toFlatzinc(b, false);
        b.append(",");
        getChild(1).toFlatzinc(b, false);
        b.append(",");
        aux.toFlatzinc(b, false);
        b.append(");");
    }
    
    public String toString() {
        return "count("+getChild(0)+","+getChild(1)+")";
    }
    
    public void toMinizinc(StringBuilder b, boolean bool_context)
    {
        b.append("count(");
        getChild(0).toMinizinc(b, false);
        b.append(", ");
        getChild(1).toMinizinc(b, false);
        b.append(")");
    }
}
