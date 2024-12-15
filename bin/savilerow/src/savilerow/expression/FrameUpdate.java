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

import savilerow.CmdFlags;
import savilerow.model.SymbolTable;

// Frame Update constraint.
 
//  frameUpdate(source, target, sourceIndices, targetIndices)


public class FrameUpdate extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public FrameUpdate(ASTNode a, ASTNode b, ASTNode c, ASTNode d) {
        super(a, b, c, d);
    }

    public ASTNode copy() {
        return new FrameUpdate(getChild(0), getChild(1), getChild(2), getChild(3));
    }

    public boolean isRelation() { return true; }
    
    public boolean typecheck(SymbolTable st) {
        for (int i=0; i < 4; i++) {
            if (!getChild(i).typecheck(st)) {
                return false;
            }
        }
        if(getChild(0).getDimension() < 1) {
            CmdFlags.println("ERROR: Expected matrix with at least one dimension as source matrix in frameUpdate constraint: " + this);
            return false;
        }
        if(getChild(1).getDimension() < 1) {
            CmdFlags.println("ERROR: Expected matrix with at least one dimension as target matrix in frameUpdate constraint: " + this);
            return false;
        }
        if(getChild(2).getDimension() != 1) {
            CmdFlags.println("ERROR: Expected one-dimensional matrix for sourceIndices in frameUpdate constraint: " + this);
            return false;
        }
        if(getChild(3).getDimension() != 1) {
            CmdFlags.println("ERROR: Expected one-dimensional matrix for targetIndices in frameUpdate constraint: " + this);
            return false;
        }
        return true;
    }
    
    @Override
    public ASTNode simplify() {
        //  Also needs to check for constant matrices in cmstore.
        for(int i=0; i<4; i++) {
            if(! getChild(i).isMatrixLiteral()) {
                return null;
            }
        }
        
        // If the dimensions of the source and target matrices are available,
        // then rewrite to FrameUpdateFlat with a block size and flattened matrices. 
        // Also shift the sourceIndices and targetIndices to match the outer index set ofthe
        // source and target matrices. 
        
        ArrayList<ASTNode> idxsource=getChild(0).getIndexDomains();
        ArrayList<ASTNode> idxtarget=getChild(1).getIndexDomains();
        
        ArrayList<Intpair> outerindexset=idxsource.get(0).getIntervalSet();
        long numblocks=Intpair.numValues(outerindexset);
        
        assert outerindexset.equals(idxtarget.get(0).getIntervalSet()) : "Mismatch between indexing of source and target in frameUpdate constraint.";
        
        if(outerindexset.size()!=1 || outerindexset.get(0).lower!=1 || outerindexset.get(0).upper!=numblocks) {
            assert false : "Source and target matrices must be indexed by int(1..n) in frameUpdate constraint.";
            //   Later make a mapping to shift the index variables.
        }
        
        long blocksize=1;
        for(int i=1; i<idxsource.size(); i++) {
            long p=Intpair.numValues(idxsource.get(i).getIntervalSet());
            blocksize=blocksize*p;
        }
        
        long blocksize2=1;
        for(int i=1; i<idxtarget.size(); i++) {
            long p=Intpair.numValues(idxtarget.get(i).getIntervalSet());
            blocksize2=blocksize2*p;
        }
        
        assert blocksize==blocksize2 : "Mismatch between block sizes of source and target in frameUpdate constraint.";
        
        return new FrameUpdateFlat(new Flatten(getChild(0)), new Flatten(getChild(1)), getChild(2), getChild(3), NumberConstant.make(blocksize));
    }
    
    public String toString() {
        return "frameUpdate(" + getChild(0) + "," + getChild(1) + "," + getChild(2) + "," + getChild(3) + ")";
    }
}
