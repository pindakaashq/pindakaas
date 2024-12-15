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
import java.util.HashMap;

import savilerow.CmdFlags;
import savilerow.expression.*;
import savilerow.model.Model;

// Turn MatrixDeref containing decision-variable indices into one-dimensional 
// element function.

public class TransformMatrixDeref extends TreeTransformerBottomUpNoWrapper
{
    boolean propagate;
    public TransformMatrixDeref(Model _m, boolean _propagate) {
        super(_m);
        propagate=_propagate;
    }
    
    protected NodeReplacement processNode(ASTNode curnode) {
	    if(curnode instanceof MatrixDeref || curnode instanceof SafeMatrixDeref)
        {
            // Find out if it needs to be translated to element (safe element)
            boolean hasVariableChildren=false;
            for(int i=1; i<curnode.numChildren(); i++) {
                if(curnode.getChild(i).getCategory()==ASTNode.Decision) {
                    hasVariableChildren=true; break;
                }
            }
            
            // If it needs to be translated...
            if(hasVariableChildren) {
                ASTNode el=matrixDerefToElement(curnode);
                // Put the element function in place of the MatrixDeref
                return new NodeReplacement(el);
            }
        }
        return null;
	}
    
	protected ASTNode matrixDerefToElement(ASTNode matrixderef)
	{
	    ASTNode matrix=matrixderef.getChildConst(0);
	    ArrayList<ASTNode> indices = matrixderef.getChildren(1);
	    
	    ArrayList<ASTNode> matdimensions;
	    
	    //  Does not handle case where matrix is a slice, or a function returning a matrix. 
	    //  Therefore needs to be called after destroyMatrices and simplify.
	    
	    if(matrix instanceof Identifier) {
	        matdimensions=((MatrixDomain) m.global_symbols.getDomain(matrix.toString())).getMDIndexDomains();
	    }
	    else {
	        assert matrix instanceof CompoundMatrix || matrix instanceof EmptyMatrix;
	        matdimensions=matrix.getIndexDomains();
	    }
	    
	    ////////////////////////////////////////////////////////////////////////
	    // First identify the constant indices and use them to slice out
	    // a multi-dimensional slice of the matrix.
	    
	    ArrayList<ASTNode> constant_indices = new ArrayList<ASTNode>();
	    ArrayList<ASTNode> variable_indices = new ArrayList<ASTNode>();
	    ArrayList<Integer> variable_indices_indices = new ArrayList<Integer>();   // The indices of the variables in indices.
	    
	    for(int i=0; i<indices.size(); i++)
	    {
	        ASTNode e=indices.get(i);
	        if(e.isConstant())
	        {
	            long a=e.getValue();
	            constant_indices.add(NumberConstant.make(a));
	            
	            if(! matdimensions.get(i).containsValue(a)) {
	                return NumberConstant.make(0);   /// Why is this OK when it's not a safematrixderef?
	            }
	        }
	        else
	        {
	            // Also need to put a .. into constant indices for the slice.
	            constant_indices.add(new IntegerDomain(new Range(null, null)));
	            variable_indices.add(e);
	            variable_indices_indices.add(i);
	        }
	    }
	    
	    matrixderef.getChild(0).setParent(null);
	    ASTNode matrixslice=new MatrixSlice(m, matrixderef.getChild(0), constant_indices);
	    
	    TransformSimplify ts=new TransformSimplify();
	    matrixslice=ts.transform(matrixslice);
	    
	    if(!matrixslice.isRegularMatrix()) {
	        CmdFlags.errorExit("Cannot index irregular matrix with decision variable expressions: "+matrixderef, "Irregular dimensions must be indexed by constant, parameter or quantifier expressions.", "See documentation for more detail.");
	    }
	    
	    long[] matdimensions2=new long[matdimensions.size()];
	    
	    ArrayList<ArrayList<Intpair>> matindexsets=new ArrayList<ArrayList<Intpair>>();
	    
	    for(int i=0; i<matdimensions2.length; i++)
	    {
	        ArrayList<Intpair> intervalset=matdimensions.get(i).getIntervalSet();
	        matindexsets.add(intervalset);
	        matdimensions2[i]=Intpair.numValues(intervalset);
	    }
	    
	    long totalArraySize=1;   // total number of elements in the array
	    
	    ArrayList<ASTNode> sumVars=new ArrayList<ASTNode>();
	    ArrayList<Long> sumWeights=new ArrayList<Long>();
	    
        for(int j=0; j<variable_indices_indices.size(); j++)
	    {
	        int i=variable_indices_indices.get(j);
	        totalArraySize=totalArraySize*matdimensions2[i];
	        
	        // find product of rest of array dimensions from i+1 ..n
	        long prod=1;
	        for(int k=i+1; k<matdimensions2.length; k++)
	        {
	            if(!(constant_indices.get(k) instanceof NumberConstant)) {
	                prod=prod*matdimensions2[k];
	            }
	        }
	        sumWeights.add(prod);
	        
	        ASTNode idx=indices.get(i).copy();
	        
	        // Shift or map idx to be contiguous from 0
	        
	        ArrayList<Intpair> indexset=matindexsets.get(i);
	        long indexsetsize=matdimensions2[i];
	        
	        if(indexsetsize!=0) {
	            //  Non-empty.
	            if(indexset.size()>1) {
                    // Not contiguous, needs a Mapping.
                    HashMap<Long,Long> mapping=new HashMap<Long,Long>();
                    long count=0;
                    if(j==variable_indices_indices.size()-1) {
                        count=1;     //  Last variable index, and base 1 target, so start indexing at 1.
                    }
                    for(int k=0; k<indexset.size(); k++) {
                        for(long l=indexset.get(k).lower; l<=indexset.get(k).upper; l++) {
                            mapping.put(l, count);
                            count++;
                        }
                    }
                    
                    idx=new Mapping(mapping, idx);
                }
                else {
                    // A single interval.
                    if(indexset.get(0).lower!=0) {
                        idx=BinOp.makeBinOp("-", idx, NumberConstant.make(indexset.get(0).lower));
                    }
                    if(j==variable_indices_indices.size()-1) {
                        idx=BinOp.makeBinOp("+", idx, NumberConstant.make(1));
                    }
                }
	        }
	        else if(j==variable_indices_indices.size()-1) {
	            idx=BinOp.makeBinOp("+", idx, NumberConstant.make(1));
	        }
	        
	        sumVars.add(idx);
	    }
	    
	    ASTNode index_expr=new WeightedSum(sumVars, sumWeights);
	    
		// Make the element constraint
		ASTNode element;
		if(matrixderef instanceof SafeMatrixDeref) {
            element= new SafeElementOne(new Flatten(matrixslice), index_expr);
        }
        else {
            element= new ElementOne(new Flatten(matrixslice), index_expr);
        }
        
		return element;
	}
}
