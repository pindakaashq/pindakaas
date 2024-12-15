package savilerow.treetransformer;
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

import savilerow.expression.*;
import savilerow.model.Model;

public class TransformMatrixIndexedMatrix extends TreeTransformerBottomUpNoWrapper
{
    ASTNode matid;
    
    long numindices;
    
    public TransformMatrixIndexedMatrix(String matname, Model _m) {
        super(_m);
        matid=new Identifier(m, matname);
        
        ASTNode matrixdomain=m.global_symbols.getDomain(matname);
        
        ASTNode replmatrixdom=flattenMatrixDimensions(matrixdomain);
        
        numindices=replmatrixdom.numChildren()-3;
        
        m.global_symbols.setDomain(matname, replmatrixdom);
    }
    
    // Returns a matrix domain with no matrices in its indices. 
    ASTNode flattenMatrixDimensions(ASTNode matdom) {
        assert matdom instanceof MatrixDomain;
        ArrayList<ASTNode> newindices=new ArrayList<ASTNode>();
        for(int i=3; i<matdom.numChildren(); i++) {
            if(! (matdom.getChild(i) instanceof MatrixDomain)) {
                // This is not a matrix -- just add to newindices.
                newindices.add(matdom.getChild(i));
            }
            else {
                // First recursively flatten child i.
                ASTNode flati=flattenMatrixDimensions(matdom.getChild(i));
                
                // This one is a matrix. Copy its base domain the appropriate number of times. 
                long numcopies=1;
                for(int j=3; j<flati.numChildren(); j++) {
                    ArrayList<Intpair> idxdom=flati.getChild(j).getIntervalSet();
                    numcopies=numcopies*Intpair.numValues(idxdom);
                }
                for(int k=0; k<numcopies; k++) {
                    newindices.add(matdom.getChild(i).getChild(0).copy());
                }
            }
        }
        
        return new MatrixDomain(matdom.getChild(0), newindices, matdom.getChild(1), matdom.getChild(2));
    }
    
    protected NodeReplacement processNode(ASTNode curnode) {
        if(! (curnode.getParent() instanceof Tag) ) {
            // Slice
            if(curnode instanceof MatrixSlice && curnode.getChild(0).equals(matid) ) {
                ArrayList<ASTNode> idx=curnode.getChildren(1);
                
                // Flatten each member of slice. Some may be matrices. 
                for(int i=0; i<idx.size(); i++) {
                    if(idx.get(i).getDimension()>0) {
                        idx.set(i, new Flatten(idx.get(i)));
                    }
                    else {
                        idx.set(i, CompoundMatrix.make(idx.get(i)));
                    }
                }
                
                // Put all elements in slice into one 1d matrix, then 'unpack' into arguments for a new matrix slice. 
                ArrayList<ASTNode> ctor_idx=new ArrayList<ASTNode>();
                ctor_idx.add(new Unpack(NumberConstant.make(numindices), new Cat(idx)));
                System.out.println("Replacing "+curnode+" with "+new MatrixSlice(m, curnode.getChild(0), ctor_idx));
                return new NodeReplacement(new Tag(new MatrixSlice(m, curnode.getChild(0), ctor_idx)));
            }
            
            //  Deref
            if( (curnode instanceof MatrixDeref || curnode instanceof SafeMatrixDeref) 
                && curnode.getChild(0).equals(matid) ) {
                
                ArrayList<ASTNode> idx=curnode.getChildren(1);
                
                // Flatten each member of slice. Some may be matrices. 
                for(int i=0; i<idx.size(); i++) {
                    if(idx.get(i).getDimension()>0) {
                        idx.set(i, new Flatten(idx.get(i)));
                    }
                    else {
                        idx.set(i, CompoundMatrix.make(idx.get(i)));
                    }
                }
                
                // Put all elements in deref into one 1d matrix, then 'unpack' into arguments for a new matrix deref. 
                ArrayList<ASTNode> ctor_idx=new ArrayList<ASTNode>();
                ctor_idx.add(new Unpack(NumberConstant.make(numindices), new Cat(idx)));
                if(curnode instanceof MatrixDeref) {
                    System.out.println("Replacing "+curnode+" with "+new MatrixDeref(curnode.getChild(0), ctor_idx));
                    return new NodeReplacement(new Tag(new MatrixDeref(curnode.getChild(0), ctor_idx)));
                }
                else {
                    System.out.println("Replacing "+curnode+" with "+new SafeMatrixDeref(curnode.getChild(0), ctor_idx));
                    return new NodeReplacement(new Tag(new SafeMatrixDeref(curnode.getChild(0), ctor_idx)));
                }
            }
        }
        
        return null;
    }
    
}
