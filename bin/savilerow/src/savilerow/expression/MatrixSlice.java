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
import savilerow.model.*;

public class MatrixSlice extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    // First child is a reference to the matrix.
    // Other children are InfiniteIntegerDomain ("..") or
    // arithmetic expression of anything except decision variables. 
    protected transient Model m;
    
    public MatrixSlice(Model _m, ASTNode id, ArrayList<ASTNode> ran)
    {
        super(id, ran.toArray(new ASTNode[ran.size()]));
        m=_m;
    }
    
    public boolean hasModel() {
        return true;
    }
    public Model getModel() {
        return m;
    }
    public void setModel(Model _m) {
        m=_m;
    }
    
    public ASTNode copy()
    {
        return new MatrixSlice(m, getChild(0), getChildren(1));
    }
    public boolean typecheck(SymbolTable st) {
        for(ASTNode child :  getChildren()) {
            if(!child.typecheck(st))
                return false;    
        }
        for(int i=1; i<numChildren(); i++) {
            if(getChild(i).getCategory()>ASTNode.Quantifier) {
                //CmdFlags.println("ERROR: Matrix slice may not contain decision variables in indices:");
                //CmdFlags.println("ERROR: "+this);
                //return false;
            }
        }
        if(numChildren()-1 != getChild(0).getDimension()) {
            CmdFlags.println("ERROR: Number of indices in matrix slice does not match dimensions of matrix:");
            CmdFlags.println("ERROR: "+this);
            return false;
        }
        return true;
    }
    
    public boolean typecheck2(SymbolTable st) {
        for(int i=0; i<numChildren(); i++) {
            if(! getChild(i).typecheck2(st)) return false;
        }
        // Check that each index is either an 'Unpack' or a scalar or ".."
        for(int i=1; i<numChildren(); i++) {
            if( !(getChild(i) instanceof Unpack) && getChild(i).getDimension()>0) {
                System.out.println("ERROR: In matrix slice "+this+", index \""+getChild(i)+"\" is a matrix. Scalar types int and bool are allowed here.");
                return false;
            }
        }
        return true;
    }
    
    public ASTNode simplify() {
        //  Check for Unpack functions in the indices.
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
                    
                    return new MatrixSlice(m, getChild(0), newidx);
                }
                // In the case where there is an Unpack but it can't be dealt with, then delay.
                return null;
            }
        }
        
        // Check the indices
        // If they are all constant then attempt to evaluate the MatrixSlice.
        // If there is a decision expression in an index then MatrixSlice will be rewritten into matrix comprehension(s).
        boolean all_const=true;
        boolean decisionvar=false;
        for(int i=1; i<numChildren(); i++) {
            int cat=getChild(i).getCategory();
            if(cat>ASTNode.Constant) {
                all_const=false;
            }
            if(cat==ASTNode.Decision) {
                decisionvar=true;
            }
        }
        
        if(all_const) {
            // Simplify if first child is a matrix literal. 
            ASTNode mat=getChildConst(0);
            if(mat instanceof CompoundMatrix || mat instanceof EmptyMatrix) {
                ASTNode eval=evaluateSlice(mat, getChildren(1));
                return (eval==null)?null:eval;
            }
        }
        
        if(decisionvar) {
            // Rewrite into matrix comprehensions (to construct the dimensions with ..) and matrix indexing.
            
            ArrayList<ASTNode> comprehensionvars=list();
            ArrayList<ASTNode> matderef=list();
            
            for(int i=1; i<numChildren(); i++) {
                if(getChild(i).isSet()) {
                    ASTNode newid=new Identifier(m, m.global_symbols.newAuxId());  //  Make a new unique variable name.
                    comprehensionvars.add(newid);
                    matderef.add(newid);
                }
                else {
                    comprehensionvars.add(null);
                    matderef.add(getChild(i));
                }
            }
            
            getChild(0).setParent(null);   //  No copy for the SafeMatrixDeref. Later uses of getChild(0) will copy. 
            ASTNode tmp=new SafeMatrixDeref(getChild(0), matderef);
            
            // Now wrap the matrix deref with comprehensions to construct the slice dimensions.
            
            // Need matrix dimensions to build the comprehensions. 
            ASTNode matindices=new Indices(getChild(0));
            
            for(int i=numChildren()-1; i>=1; i--) {
                if(getChild(i).isSet()) {
                    ASTNode indexdom=new MatrixDeref(matindices, list(NumberConstant.make(i)));  // Get the index domain for this dimension from the list of indices.
                    
                    //  Wrap tmp with a comprehension to construct dimension i. 
                    
                    tmp=new ComprehensionMatrix(tmp, list(new ComprehensionForall(comprehensionvars.get(i-1), indexdom)), new BooleanConstant(true), indexdom);
                }
            }
            return tmp;
        }
        
        return null;
    }
    
    // recursively evaluate the slice. Returns null if the slice is undefined. 
    public static ASTNode evaluateSlice(ASTNode compound_matrix, ArrayList<ASTNode> indices) {
        if(indices.size()==0) {
            assert !(compound_matrix instanceof CompoundMatrix || compound_matrix instanceof EmptyMatrix);
            return compound_matrix;
        }
        
        ASTNode sliceindex=indices.get(0);
        
        if(compound_matrix instanceof EmptyMatrix) {
            // Construct new matrix domain for empty matrix.
            // First get the matrix domain for compound_matrix (which is itself an empty matrix)
            ASTNode matdom=compound_matrix.getChild(0);
            
            // Get indices
            ArrayList<ASTNode> empty_idx=matdom.getChildren(3);
            
            assert empty_idx.size()==indices.size();
            
            for(int i=empty_idx.size()-1; i>=0; i--) {
                if(! indices.get(i).equals(new IntegerDomain(new Range(null, null)))) {
                    // If indices.get(i) is a constant, remove that dimension.  
                    empty_idx.remove(i);
                }
            }
            
            return new EmptyMatrix(new MatrixDomain(compound_matrix.getChild(0).getChild(0), // get original base domain. 
                empty_idx));
        }
        
        // Must be a compound matrix from here on. 
        if(sliceindex.isSet()) {
            assert ! sliceindex.isFiniteSetUpper() && ! sliceindex.isFiniteSetLower();  //  Should be ..
            ArrayList<ASTNode> newcm=new ArrayList<ASTNode>();
            
            ArrayList<ASTNode> restindices=new ArrayList<ASTNode>(indices);
            restindices.remove(0);
            
            for(int i=1; i<compound_matrix.numChildren(); i++) {
                ASTNode tmp=evaluateSlice(compound_matrix.getChildConst(i), restindices);
                if(tmp==null) return null;
                newcm.add(tmp);
            }
            return new CompoundMatrix(compound_matrix.getChild(0), newcm);   // Take index domain from original CM.
        }
        else {
            // This index must be a constant
            ArrayList<Intpair> cmindex;
            if(compound_matrix instanceof CompoundMatrix) {
                cmindex=compound_matrix.getChild(0).getIntervalSet();
            }
            else if (compound_matrix instanceof EmptyMatrix) {
                cmindex=new ArrayList<Intpair>();
            }
            else {
                cmindex=null;
            }
            
            long val=sliceindex.getValue();
            long idxval=Intpair.location(cmindex, val);
            
            if(idxval==-1) {
                // Matrix is indexed out of range.  Undefined. Delay evaluation. 
                return null;
            }
            
            ArrayList<ASTNode> restindices=new ArrayList<ASTNode>(indices);
            restindices.remove(0);
            
            return evaluateSlice(compound_matrix.getChildConst(((int) idxval)+1), restindices);
        }
    }
    
    public ArrayList<ASTNode> getIndexDomains() {
        if(getChild(0) instanceof Identifier && getChild(0).getCategory()==ASTNode.Decision) {
            //  For the sake of evaluating IndexOf functions. 
            ASTNode matrixdomain=m.global_symbols.getDomain(getChild(0).toString());
            if(matrixdomain != null && matrixdomain instanceof MatrixDomain) {
                ArrayList<ASTNode> idx=matrixdomain.getChildren(3);
                //  Remove dimensions that the slice will remove.
                ArrayList<ASTNode> idx2=new ArrayList<>();
                for(int i=1; i<numChildren(); i++) {
                    //  If the index is int(..) in the slice, then copy over the index domain.
                    ArrayList<Intpair> a=getChild(i).getIntervalSet();
                    if(a!=null && a.size()==1 && a.get(0).lower==Long.MIN_VALUE && a.get(0).upper==Long.MAX_VALUE) {
                        idx2.add(idx.get(i-1));
                    }
                }
                return idx2;
            }
        }
        return null;
    }
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
    {
        assert !bool_context;
        getChild(0).toMinion(b, false);
        b.append("[");
        for(int i=1; i<numChildren(); i++)
        {
            getChild(i).toMinion(b, false);
            if(i<numChildren()-1) b.append(",");
        }
        b.append("]");
    }
    public Intpair getBounds() {
        return getChild(0).getBounds();
    }
    @Override
    public int getDimension() {
        int count=0;
        for(int i=1; i<numChildren(); i++) {
            if(getChild(i).isSet()) {
                count++;
            }
        }
        return count;
    }
    
    public String toString() {
        String st=getChild(0).toString()+"[";
        for(int i=1; i<numChildren(); i++) {
            st=st+getChild(i);
            if(i<numChildren()-1) st+=",";
        }
        return st+"]";
    }
    
    // Element requires this. 
    public boolean isRelation() {
        return getChild(0).isRelation();
    }
    public boolean strongProp() {
        for(int i=0; i<numChildren(); i++) {
            if((!getChild(i).isSet()) && (!getChild(i).strongProp())) {
                return false;
            }
        }
        return true;
    }
    public boolean isNumerical() {
        return getChild(0).isNumerical();
    }
}
