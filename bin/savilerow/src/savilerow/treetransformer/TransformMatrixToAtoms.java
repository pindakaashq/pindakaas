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

//  Transform a matrix of decision variables into individual decision vars, and 
//  all matrixderefs, slices and atomic identifiers need to be changed as well.

public class TransformMatrixToAtoms extends TreeTransformerBottomUpNoWrapper
{
    ASTNode matid;
    
    ArrayList<ASTNode> indexdoms;
    
    ASTNode matrixdomain;
    
    ASTNode matrixliteral;
    
    public TransformMatrixToAtoms(String matname, Model _m) {
        super(_m);
        matid=new Identifier(m, matname);
        matrixdomain=m.global_symbols.getDomain(matname);
        
        indexdoms=matrixdomain.getChildren(3);
        
        // Introduce new variables for each entry in the matrix. 
        enumerateMatrix(new ArrayList<ASTNode>(indexdoms), matname, matrixdomain.getChild(0), matid, new ArrayList<Long>());
        
        m.global_symbols.deleteMatrix(matname);   // Not just a straightforward deletion, need to keep it for parsing
        
        // Make a matrix literal for the whole matrix.
        matrixliteral=enumerateMatrixLiteral(indexdoms, matname, m, matrixdomain.getChild(0).isBooleanSet());
    }
    
    private final static String fmtstr(long i) {
        if(i>=0) {
            return String.format("%05d",i);
        }
        else {
            //  Negative indicated by n.
            return "n"+String.format("%05d",-i);
        }
    }
    
    //  create vars M_1_1 for M[1,1]
    private void enumerateMatrix(ArrayList<ASTNode> idxdoms, String build, ASTNode basedom, ASTNode baseid, ArrayList<Long> indices) {
        if(idxdoms.size()==0) {
            m.global_symbols.newVariable(build, basedom.copy(), ASTNode.Decision, baseid, indices);
        }
        else {
            ArrayList<ASTNode> localindexdoms=new ArrayList<ASTNode>(idxdoms);
            ASTNode idx=localindexdoms.remove(0);
            ArrayList<Intpair> valset=idx.getIntervalSet();
            for(int i=0; i<valset.size(); i++) {
                for(long val=valset.get(i).lower; val<=valset.get(i).upper; val++) {
                    String fmtint=fmtstr(val);
                    String newbuild=build+"_"+fmtint;
                    indices.add(val);
                    enumerateMatrix(localindexdoms, newbuild, basedom, baseid, indices);
                    indices.remove(indices.size()-1);
                }
            }
        }
    }
    
    // Build a matrix literal for the whole matrix. 
    public static ASTNode enumerateMatrixLiteral(ArrayList<ASTNode> idxdoms, String build, Model m, boolean isBool) {
        if(idxdoms.size()==0) {
            return new Identifier(m, build);
        }
        else {
            ArrayList<ASTNode> localindexdoms=new ArrayList<ASTNode>(idxdoms);
            ASTNode idx=localindexdoms.remove(0);
            ArrayList<Intpair> valset=idx.getIntervalSet();
            
            ArrayList<ASTNode> compoundmatrix=new ArrayList<ASTNode>();
            for(int i=0; i<valset.size(); i++) {
                for(long val=valset.get(i).lower; val<=valset.get(i).upper; val++) {
                    String fmtint=fmtstr(val);
                    String newbuild=build+"_"+fmtint;
                    compoundmatrix.add(enumerateMatrixLiteral(localindexdoms, newbuild, m, isBool));
                }
            }
            if(compoundmatrix.size()>0) {
                return new CompoundMatrix(idx, compoundmatrix);  // Make new cm with index domain
            }
            else {
                // Empty in this dimension. 
                ASTNode basedom=isBool?new BooleanDomain(new EmptyRange()):new IntegerDomain(new EmptyRange());
                return new EmptyMatrix(new MatrixDomain(basedom, new ArrayList<ASTNode>(idxdoms)));
            }
        }
    }
    
    // New implementation making use of matrixliteral and methods in MatrixSlice and MatrixDeref
    protected NodeReplacement processNode(ASTNode curnode) {
        
        // Slice
        if(curnode instanceof MatrixSlice && curnode.getChild(0).equals(matid) ) {
            ArrayList<ASTNode> slice=curnode.getChildren(1);
            
            ASTNode cm=MatrixSlice.evaluateSlice(matrixliteral, slice); 
            
            if(cm==null) {
                // Slice cannot be evaluated because some index is out of bounds.
                // Put a copy of the matrix literal into the slice and leave it un-evaluated.
                return new NodeReplacement(new MatrixSlice(m, matrixliteral, slice));
            }
            
            return new NodeReplacement(cm);
        }
        
        //  Deref
        if( (curnode instanceof MatrixDeref || curnode instanceof SafeMatrixDeref) 
	        && curnode.getChild(0).equals(matid) ) {
	        
	        ArrayList<ASTNode> indices=curnode.getChildren(1);
	        
	        ASTNode df=null;
	        
	        boolean constIndices=true;
	        for(int i=1; i<curnode.numChildren(); i++) {
	            if(! curnode.getChild(i).isConstant() ) {
	                constIndices=false;
	                break;
	            }
	        }
	        
	        if(constIndices) {
                if(curnode instanceof MatrixDeref) {
                    df=MatrixDeref.derefCompoundMatrix(matrixliteral, indices);
                }
                else {
                    df=SafeMatrixDeref.derefCompoundMatrix(matrixliteral, indices);
                }
	        }
	        
	        if(df==null) {
	            // Deref cannot be evaluated because some index is out of bounds, or some index contains a decision variable. 
	            // Put a new copy of the matrix literal into the deref and leave it unevaluated.
	            if(curnode instanceof MatrixDeref) {
	                return new NodeReplacement(new MatrixDeref(matrixliteral, indices));
	            }
	            else {
	                return new NodeReplacement(new SafeMatrixDeref(matrixliteral, indices));
	            }
            }
            
            return new NodeReplacement(df);
        }
        
        if(curnode instanceof IsMatrixSliceDefined && curnode.getChild(0).equals(matid)) {
            //  Quick check if the indexing expressions are constants.
            //  We know the matrix is regular. 
            boolean all_const=true;
            for(int i=1; i<curnode.numChildren(); i++) {
                if(curnode.getChild(i).getCategory()>ASTNode.Constant) {
                    all_const=false;
                    break;
                }
            }
            
            if(all_const) {
                ASTNode eval=MatrixSlice.evaluateSlice(matrixliteral, curnode.getChildren(1));
                return new NodeReplacement(new BooleanConstant(eval!=null));
            }
            
            return new NodeReplacement(new IsMatrixSliceDefined(m, matrixliteral, curnode.getChildren(1)));
        }
        
        // Neither slice nor deref nor isdefined
        if(curnode instanceof Identifier && curnode.equals(matid)
            && !(curnode.getParent() instanceof MatrixDeref)
            && !(curnode.getParent() instanceof SafeMatrixDeref)
            && !(curnode.getParent() instanceof MatrixSlice)
            && !(curnode.getParent() instanceof IsMatrixSliceDefined)
            ) {
            return new NodeReplacement(matrixliteral);
        }
        return null;
    }
    
}
