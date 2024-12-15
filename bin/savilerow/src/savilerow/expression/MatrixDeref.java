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

import savilerow.CmdFlags;
import savilerow.model.SymbolTable;

public class MatrixDeref extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    // The first child is a matrix reference, the rest are indices.
    public MatrixDeref(ASTNode mat, ArrayList<ASTNode> ind) {
        super(mat, ind.toArray(new ASTNode[ind.size()]));
    }
    // Just one dimension
    public MatrixDeref(ASTNode mat, ASTNode ind) {
        super(mat, ind);
    }
    
    public ASTNode copy()
    {
        return new MatrixDeref(getChild(0), getChildren(1));
    }
    
    public boolean isRelation() {
        // Is first child a matrix of bool
        return getChild(0).isRelation();
    }
    public boolean strongProp() {
        for(int i=0; i<numChildren(); i++) {
            if(!getChild(i).strongProp()) {
                return false;
            }
        }
        return true;
    }
    public boolean isNumerical() {
        return !getChild(0).isRelation() && !getChild(0).isSet();
    }
    public boolean isSet() {
        return getChild(0).isSet();
    }
    
    public Intpair getBounds()
    {
        return getChild(0).getBounds();
    }
    public ArrayList<Intpair> getIntervalSetExp() {
        return getChild(0).getIntervalSetExp();
    }
    public boolean toFlatten(boolean propagate) {
        if(this.isNumerical()) {
            return true;
        }
        return super.toFlatten(propagate);  // Hand over to ASTNode.toFlatten
    }
    
    public ASTNode simplify() {
        for(int i=1; i<numChildren(); i++) {
            if(getChild(i) instanceof Unpack) {
                ArrayList<ASTNode> indices=((Unpack)getChild(1)).items();
                if(indices!=null) {
                    detachChildren();
                    ArrayList<ASTNode> newidx=new ArrayList<ASTNode>(numChildren()+indices.size()-2);
                    
                    for(int j=1; j<i; j++) {
                        newidx.add(getChild(j));
                    }
                    newidx.addAll(indices);
                    for(int j=i+1; j<numChildren(); j++) {
                        newidx.add(getChild(j));
                    }
                    
                    return new MatrixDeref(getChild(0), newidx);
                }
                // In the case where there is an Unpack but it can't be dealt with, then delay.
                return null;
            }
        }
        
        boolean hasVariableIndices=false;
        for(int i=1; i<numChildren(); i++) {
            if(getChild(i).getCategory()!=ASTNode.Constant) {
                hasVariableIndices=true;
                break;
            }
        }
        
        if(!hasVariableIndices) {
            ASTNode mat=getChildConst(0);
            if(mat instanceof CompoundMatrix || mat instanceof EmptyMatrix) {
                ASTNode df=MatrixDeref.derefCompoundMatrix(mat, getChildren(1));
                return (df==null)?null:df;
            }
        }
        return null;
    }
    
    public static ASTNode derefCompoundMatrix(ASTNode cm, ArrayList<ASTNode> indices) {
        for(int i=0; i<indices.size(); i++) {
            if(! (cm instanceof CompoundMatrix) ) {
                // Can't deref cm any further. 
                return null;
            }
            
            ASTNode idxdom=cm.getChild(0);
            long idx=indices.get(i).getValue();
            
            int childidx=(int) Intpair.location(idxdom.getIntervalSet(), idx);
            
            if(childidx==-1) {
                // Out of bounds -- allow the undef constraint to deal with this case.
                return null;
            }
            int childno=childidx+1;
            
            // Actually do the deref. 
            cm=cm.getChildConst(childno);
        }
        
        return cm;
    }
    
    public boolean typecheck(SymbolTable st) {
        for(int i=0; i<numChildren(); i++) {
            if(! getChild(i).typecheck(st)) return false;
        }
        
        // Check right number of dimensions (actually number of index slots -- different when matrix indexed by matrix). 
        if(getChild(0).getDimension() != numChildren()-1) {
            System.out.println("ERROR: Dimension mismatch in matrix deref: "+this);
            return false;
        }
        
        // check type of each index -- must be numerical or relational.
        for(int i=1; i<numChildren(); i++) {
            if( !getChild(i).isNumerical() && !getChild(i).isRelation() ) {
                System.out.println("ERROR: In matrix deref "+this+", index "+getChild(i)+" is not numerical or relational.");
                return false;
            }
        }
        return true;
    }
    
    public boolean typecheck2(SymbolTable st) {
        for(int i=0; i<numChildren(); i++) {
            if(! getChild(i).typecheck2(st)) return false;
        }
        // Check that each index is either an 'Unpack' or a scalar. 
        for(int i=1; i<numChildren(); i++) {
            if( !(getChild(i) instanceof Unpack) && getChild(i).getDimension()>0) {
                System.out.println("ERROR: In matrix deref "+this+", index \""+getChild(i)+"\" is a matrix. Scalar types int and bool are allowed here.");
                return false;
            }
        }
        return true;
    }
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
    {
        if(bool_context) {
            // If it's contained in and or or, stick it inside an equal constraint.
            if(CmdFlags.getUseBoundVars() && this.exceedsBoundThreshold() ) {
                b.append("eq(");
            }
            else {
                b.append("w-literal(");
            }
        }
        
        getChild(0).toMinion(b, false);
        b.append("[");
        for(int i=1; i<numChildren(); i++) {
            getChild(i).toMinion(b, false);
            if(i<numChildren()-1) b.append(",");
        }
        b.append("]");
        
        if(bool_context) {
            b.append(",1)");
        }
    }
    
    public String toString() {
        String st=getChild(0).toString()+"[";
        for(int i=1; i<numChildren(); i++) { 
            st=st+getChild(i);
            if(i<numChildren()-1) st+=", ";
        }
        return st+"]";
    }
    public void toMinizinc(StringBuilder b, boolean bool_context)
    {
        getChild(0).toMinizinc(b, bool_context);
        b.append("[");
        for(int i=1; i<numChildren(); i++) {
            getChild(i).toMinizinc(b, false);
            if(i<numChildren()-1) b.append(",");
        }
        b.append("]");
    }
}
