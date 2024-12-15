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

import savilerow.model.Model;

//  For a matrix slice or matrix deref (possibly of irregular matrix), indexed
//  by non-decision expressions, is it defined? If so, this type evaluates to 
//  true, otherwise false. 

public class IsMatrixSliceDefined extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    // First child is a reference to the matrix.
    // Other children are InfiniteIntegerDomain ("..") or
    // arithmetic expression of anything except decision variables. 
    protected transient Model m;
    
    public IsMatrixSliceDefined(Model _m, ASTNode id, ArrayList<ASTNode> ran)
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
        return new IsMatrixSliceDefined(m, getChild(0), getChildren(1));
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
                    
                    return new IsMatrixSliceDefined(m, getChild(0), newidx);
                }
                // In the case where there is an Unpack but it can't be dealt with, then delay.
                return null;
            }
        }
        
        ASTNode matrix=getChild(0);
        ArrayList<ASTNode> indices = getChildren(1);
        assert matrix.getDimension()==indices.size();
        
        //  Simple cases where indexing is clearly defined. 
        
        ASTNode matconst=getChildConst(0);
        
        // Indexing a decision variable matrix, or indexing a regular constant matrix. 
        if(  (matconst instanceof Identifier && matconst.getCategory()==ASTNode.Decision) 
            || (matconst.getCategory()==ASTNode.Constant && matconst.isRegularMatrix()) ) {
            // Decision variable matrix, must be regular and must have constant index domains.
            // OR Regular constant matrix. 
            ArrayList<ASTNode> midx=matconst.getIndexDomains();
            boolean oob=false;   // Found a potentially out of bounds index
            for(int i=0; i<midx.size(); i++) {
                ArrayList<Intpair> b;
                if(getChild(i+1) instanceof SafeMatrixDeref) {
                    b=getChild(i+1).getChild(0).getIntervalSetExp();  // Avoid inconvenient default value -- will be disallowed by definedness cts
                }
                else {
                    b=getChild(i+1).getIntervalSetExp();
                }
                
                ArrayList<Intpair> idxb=midx.get(i).getIntervalSet();
                
                ArrayList<Intpair> diff=Intpair.setDifference(b, idxb);   // set of values used for indexing minus index domain. 
                
                if(diff.size()>0) { 
                    oob=true;
                    break;
                }
            }
            
            if(!oob) {
                return new BooleanConstant(true);
            }
        }
        
        // Two cases for decision variable expressions (in indices) or not. 
        
        boolean decisionIdxs=false;  // Do any index expressions contain decision variables?
        // Find the items in indices that are _not_  a set (i.e.  '..')
        ArrayList<Intpair> finite_items=new ArrayList<Intpair>();
        for(int i=0; i<indices.size(); i++) {
            if(!(indices.get(i).isSet())) {
                finite_items.add(new Intpair(i+1, i+1));
                if(indices.get(i).getCategory()==ASTNode.Decision) {
                    decisionIdxs=true;
                }
            }
        }
        
        if(decisionIdxs) {
            //  Decision variables in indexing expressions.
            //  Assume matrix is regular to construct definedness constraint. 
            //   Deal with all dimensions -- dimvar is the current dimension.
            ASTNode dimvar;
            if(finite_items.size()!=1) {
                dimvar=new Identifier(m, m.global_symbols.newAuxId());
            }
            else {
                dimvar=NumberConstant.make(finite_items.get(0).lower);
            }
            
            ArrayList<ASTNode> deref_arg=new ArrayList<ASTNode>();
            deref_arg.add(dimvar);
            
            ASTNode indices_cm=CompoundMatrix.make(indices);
            
            ASTNode constraint=new InSet(new SafeMatrixDeref(indices_cm, deref_arg), 
                new SafeMatrixDeref(new Indices(matrix), deref_arg));
            
            ASTNode definedc;
            if(finite_items.size()!=1) {
                definedc=new ForallExpression(dimvar, Intpair.makeDomain(finite_items, false), constraint);
            }
            else {
                definedc=constraint;
            }
            
            //  Add error if matrix is irregular
            definedc=new And(definedc, new ErrorWhenFalse(
                new IsRegularMatrix(getChild(0)),
                "Irregular matrix indexed by decision expression: "+getChild(0)+getChildren(1)));
            return definedc;
        }
        else {
            // No decision variables in indexing expressions.
            // Check the indices
            // If they are all constant then attempt to evaluate the MatrixSlice.
            boolean all_const=true;
            for(int i=1; i<numChildren(); i++) {
                int cat=getChild(i).getCategory();
                if(cat>ASTNode.Constant) {
                    all_const=false;
                }
            }
            
            if(all_const && getChildConst(0).isMatrixLiteral()) {
                // Simplify if first child is a matrix literal. 
                ASTNode mat=getChildConst(0);
                ASTNode eval=MatrixSlice.evaluateSlice(mat, getChildren(1));
                return new BooleanConstant(eval!=null);
            }
            
            return null;
        }
    }
    
    public String toString() {
        String st="isMatrixSliceDefined(";
        for(int i=0; i<numChildren(); i++) {
            st=st+getChild(i);
            if(i<numChildren()-1) st+=",";
        }
        return st+")";
    }
    
    public boolean isRelation() {
        return true;
    }
}
