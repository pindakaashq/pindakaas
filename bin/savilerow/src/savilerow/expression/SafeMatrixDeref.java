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

// With a default value of 0.

public class SafeMatrixDeref extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    // The first child is a matrix reference, the rest are indices.
    public SafeMatrixDeref(ASTNode mat, ArrayList<ASTNode> ind) {
        super(mat, ind.toArray(new ASTNode[ind.size()]));
    }
    
    public ASTNode copy()
    {
        return new SafeMatrixDeref(getChild(0), getChildren(1));
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
        return true;  //  Assume the translation into element will give good propagation.
    }
    public boolean isNumerical() {
        return !getChild(0).isRelation() && !getChild(0).isSet();
    }
    public boolean isSet() {
        return getChild(0).isSet();
    }
    
    public Intpair getBounds()
    {
        Intpair a=getChild(0).getBounds();
        if(a.lower>0) a.lower=0;  // Add the default value.
        if(a.upper<0) a.upper=0;
        return a;
    }
    public ArrayList<Intpair> getIntervalSetExp() {
        ArrayList<Intpair> zero=new ArrayList<Intpair>(1);
        zero.add(new Intpair(0,0));
        return Intpair.union(getChild(0).getIntervalSetExp(), zero);
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
                    
                    return new SafeMatrixDeref(getChild(0), newidx);
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
                ASTNode df=SafeMatrixDeref.derefCompoundMatrix(mat, getChildren(1));
                return (df==null)?null:df;
            }
        }
        return null;
    }
    
    public static ASTNode derefCompoundMatrix(ASTNode cm, ArrayList<ASTNode> indices) {
        for(int i=0; i<indices.size(); i++) {
            if(! (cm instanceof CompoundMatrix || cm instanceof EmptyMatrix) ) {
                // Can't deref cm any further. 
                return null;
            }
            if(cm instanceof EmptyMatrix) return NumberConstant.make(0);  // Default value.
            
            // From here on its a CompoundMatrix.
            ASTNode idxdom=cm.getChild(0);
            long idx=indices.get(i).getValue();
            
            ArrayList<Intpair> idxpairs=idxdom.getIntervalSet();
            if(idxpairs==null) {
                // idxdom is not constant. Cannot deref cm any further.
                return null;
            }
            
            // Check size of index domain against number of elements in matrix.
            if(Intpair.numValues(idxpairs) != cm.numChildren()-1) {
                CmdFlags.warning("Index domain size does not match number of elements: "+cm);
            }
            
            int childidx=(int) Intpair.location(idxpairs, idx);
            
            if(childidx==-1) {
                // Out of bounds
                return NumberConstant.make(0);  // Default value. 
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
        
        // Check right number of dimensions.
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
    
    //  WARNING --- All these output methods are inaccurate because they lose the
    // 'safe' default value. 
    
    // Minion might break on this 
    // even though it will be guarded by constraints that the indices are in bounds
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
