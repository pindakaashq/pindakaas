package savilerow.model;
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
import java.util.HashMap;
import java.util.HashSet;

import savilerow.*;
import savilerow.expression.*;
import savilerow.treetransformer.TransformSimplify;

////////////////////////////////////////////////////////////////////////////////
//
//   Deduplicated store of named matrix constants.

//  No identifiers are allowed in here, hence no references to SymbolTable to be
//  updated when copying. 
//  No need for simplify, substitute or any other operation. 

public class ConstantMatrixStore 
{
    // Map names to matrix literals (may contain a matrix literal more than once)
    private HashMap<String, ASTNode> cm;

    // Names which are already written to minion
    
    private HashSet<String> already_written;
    
    // Map matrix literals to set of names.
    private HashMap<ASTNode, HashSet<String>> cm_names;
    
    public Model m;
    
    public ConstantMatrixStore(Model _m) {
        m=_m;
        cm = new HashMap<String, ASTNode>();
        cm_names = new HashMap<ASTNode, HashSet<String>>();
        already_written = new HashSet<>();
    }
    
    //  Basic housekeeping functions
    //  All changes to cm and cm_names must go through these two methods.
    private void removeEntry(String name) {
        assert cm.containsKey(name);
        ASTNode mat=cm.get(name);
        
        boolean present=cm_names.get(mat).remove(name);  // remove old matrix -> name mapping.
        assert present;
        
        if(cm_names.get(mat).isEmpty()) {
            cm_names.remove(mat);  // Empty set of names -- remove entry in cm_names.
        }
        
        cm.remove(name);
    }
    
    private void addEntry(String name, ASTNode matlit) {
        assert !cm.containsKey(name);
        
        if(cm_names.containsKey(matlit)) {
            // This matrix is equal to one that is already stored.
            // First get the stored matrix by using any one of its names from cm_names.
            ASTNode storedmat=cm.get(cm_names.get(matlit).iterator().next());
            
            cm_names.get(storedmat).add(name);
            // In cm insert a reference to the existing stored matrix literal, not matlit so matlit can be GC'd.
            cm.put(name, storedmat);
        }
        else {
            // This matrix is not equal to any existing matrix.
            HashSet<String> hs=new HashSet<String>();
            hs.add(name);
            cm_names.put(matlit, hs);
            cm.put(name, matlit);
        }
    }
    
    public ASTNode getConstantMatrix(String name) {
        assert cm.containsKey(name);
        return cm.get(name);
    }
    
    // Replace an existing entry
    public void setConstantMatrix(String name, ASTNode replacement) {
        removeEntry(name);
        addEntry(name, replacement);
    }
    
    public boolean hasConstantMatrix(String name) {
        return cm.containsKey(name);
    }
    
    public void removeConstantMatrix(String name) {
        removeEntry(name);
    }
    
    public void newConstantMatrix(String name, ASTNode mat) {
        m.global_symbols.registerConstantMatrix(name);
        
        addEntry(name, mat);
        
        if(m.global_symbols.getDomain(name) == null) {
            // There is no domain from a given. It was something like 'letting vals = [1,2,3]'
            // Construct the matrix domain.
            Intpair cont = getConstantMatrixBounds(mat);
            ASTNode basedom;
            if (cont == null) {
                if(mat.isRelation()) {
                    basedom = new BooleanDomain(new Range(NumberConstant.make(0), NumberConstant.make(0)));
                }
                else {
                    basedom = new IntegerDomain(new Range(NumberConstant.make(0), NumberConstant.make(0)));
                }
            }
            else {
                if(mat.isRelation()) {
                    basedom = new BooleanDomain(new Range(NumberConstant.make(cont.lower), NumberConstant.make(cont.upper)));
                }
                else {
                    basedom = new IntegerDomain(new Range(NumberConstant.make(cont.lower), NumberConstant.make(cont.upper)));
                }
            }
            
            ArrayList<ASTNode> indices=mat.getIndexDomainsIrregular();
            
            ASTNode matrixdom = new MatrixDomain(basedom, indices);
            
            m.global_symbols.setDomain(name, matrixdom);
        }
        else {
            // There is a domain from a previous given. Tighten the base domain.
            //  Changes the domain in-place.
            tightenConstantMatrixDomain(name, m.global_symbols.getDomain(name));
        }
    }
    
    public ASTNode newConstantMatrixDedup(ASTNode mat) {
        if(containsRefs(mat)) {
            mat=mat.copy();
            copyInRefs(mat);
        }
        
        if(cm_names.containsKey(mat)) {
            String name=cm_names.get(mat).iterator().next();
            return new Identifier(m, name);
        }
        else {
            String newname=m.global_symbols.newAuxId();
            newConstantMatrix(newname, mat);
            return new Identifier(m, newname);
        }
    }
    
    private boolean containsRefs(ASTNode mat) {
        if(mat instanceof Identifier) {
            return true;
        }
        else if(mat instanceof CompoundMatrix) {
            for(int i=1; i<mat.numChildren(); i++) {
                if(containsRefs(mat.getChild(i))) {
                    return true;
                }
            }
            return false;
        }
        else {
            return false;
        }
    }
    
    //  If the constant matrix contains any references to other constant
    //  matrices, copy the others and replace the references. 
    private void copyInRefs(ASTNode mat) {
        assert mat instanceof CompoundMatrix;
        for(int i=1; i<mat.numChildren(); i++) {
            copyInRefsInner(mat.getChild(i));
        }
    }
    
    private void copyInRefsInner(ASTNode mat) {
        if(mat instanceof Identifier) {
            ASTNode a=getConstantMatrix(mat.toString());
            mat.getParent().setChild(mat.getChildNo(), a);
            mat=a;
        }
        
        if(mat instanceof CompoundMatrix) {
            for(int i=1; i<mat.numChildren(); i++) {
                copyInRefsInner(mat.getChild(i));
            }
        }
    }
    
    private void tightenConstantMatrixDomain(String name, ASTNode dom) {
        Intpair matbnds = getConstantMatrixBounds(cm.get(name));
        
        if (matbnds != null) {
            // Matrix is not empty, therefore it has bounds, tighten the base domain.
            
            ASTNode basedom = dom.getChild(0);
            
            if (! (basedom.isBooleanSet())) {
                // If basedom were boolean, the intersect might change it to int. Can't have that.
                basedom = new Intersect(basedom, new IntegerDomain(new Range(NumberConstant.make(matbnds.lower), NumberConstant.make(matbnds.upper))));
                TransformSimplify ts = new TransformSimplify();
                basedom = ts.transform(basedom);
            }
            
            dom.setChild(0, basedom);
        }
        
        //  When the index in the given domain is int(..) and the given matrix is regular in that dimension,
        //  replace the int(..) with the index of the given matrix. 
        ArrayList<ASTNode> indices=cm.get(name).getIndexDomainsIrregular();
        for(int i=0; i<indices.size(); i++) {
            if(dom.numChildren()>i+3 && (! dom.getChild(i+3).isFiniteSet()) && indices.get(i).isFiniteSet()) {
                dom.setChild(i+3, indices.get(i));
            }
        }
    }
    
    //  For regular matrices return the size in each dimension.
    ArrayList<Long> getConstantMatrixSize(ASTNode mat) {
        ArrayList<ASTNode> idxdoms=mat.getIndexDomains();
        
        ArrayList<Long> out=new ArrayList<Long>(idxdoms.size());
        
        for(int i=0; i<idxdoms.size(); i++) {
            ArrayList<Intpair> intervals=idxdoms.get(i).getIntervalSet();
            long size=0;
            
            for(int j=0; j<intervals.size(); j++) {
                size=size+intervals.get(j).upper-intervals.get(j).lower+1L;
            }
            out.add(size);
        }
        return out;
    }
    
    // Return a list of all elements in reading order. 
    public static ArrayList<Long> getConstantMatrixContents(ASTNode mat) {
        ArrayList<Long> tmp = new ArrayList<Long>();
        if (mat instanceof CompoundMatrix || mat instanceof EmptyMatrix) {
            for (int i=1; i < mat.numChildren(); i++) {
                tmp.addAll(getConstantMatrixContents(mat.getChild(i)));
            }
        }
        else if(mat.isTuple()) {
            for(int i=1; i<=mat.getTupleLength(); i++) {
                tmp.add(mat.getValueIdx(i));
            }
        }
        else {
            // Should be a constant
            assert mat.isConstant();
            tmp.add(mat.getValue());
        }
        return tmp;
    }
    
    //   Get max and min of the values in a compound matrix/empty matrix.
    //   Why not use getBounds?
    Intpair getConstantMatrixBounds(ASTNode mat) {
        if (mat instanceof CompoundMatrix) {
            Intpair a = null;

            for (int i =1; i < mat.numChildren(); i++) {
                Intpair b = getConstantMatrixBounds(mat.getChild(i));
                if (b != null) {
                    if (a == null) {
                        a = b;
                    } else {
                        a.lower = (a.lower < b.lower) ? a.lower : b.lower;
                        a.upper = (a.upper > b.upper) ? a.upper : b.upper;
                    }
                }
            }
            return a;
        }
        else if(mat.isTuple()) {
            return mat.getBounds();
        }
        else if (mat instanceof EmptyMatrix) {
            return null;            // nothing here.
        }
        else {
            // Should be a constant
            assert mat.isConstant();
            Intpair a = new Intpair(mat.getValue(), mat.getValue());
            return a;
        }
    }
    
    // Makes lettings where a given (or letting--really??) statement has 'matrix indexed by [int(a..b)...]'
    // and we don't know a and b, but can determine it from the index domains of the letting/param constant matrix.
    public ArrayList<ASTNode> makeLettingsConstantMatrix(String matname) {
        ASTNode mat = cm.get(matname);
        ASTNode dom = m.global_symbols.getDomain(matname);
        
        ArrayList<ASTNode> idxdoms = mat.getIndexDomains();
        
        ASTNode basedom = dom.getChild(0);
        
        ArrayList<ASTNode> indexdoms = dom.getChildren(3);        // get index domains.
        
        ArrayList<ASTNode> newlettings = new ArrayList<ASTNode>();
        for (int i =0; i < indexdoms.size() && i < idxdoms.size(); i++) {
            if (indexdoms.get(i) instanceof IntegerDomain) {
                if (indexdoms.get(i).numChildren() == 1) {
                    // Check if it is of type a..b
                    
                    ASTNode range = indexdoms.get(i).getChild(0);
                    if (range instanceof Range) {
                        if (range.getChild(0) instanceof Identifier) {
                            // int(a..constant)  case.
                            long nValues=Intpair.numValues(idxdoms.get(i).getIntervalSet());
                            
                            // Compute a lower bound from the size of idxdoms.get(i)
                            ASTNode newlet = new Letting(range.getChild(0), BinOp.makeBinOp("-", range.getChild(1), NumberConstant.make(nValues-1)));
                            newlet = (new TransformSimplify()).transform(newlet);
                            newlettings.add(newlet);
                        }
                        
                        if (range.getChild(1) instanceof Identifier) {
                            // int(constant..b)
                            long nValues=Intpair.numValues(idxdoms.get(i).getIntervalSet());
                            
                            // Compute an upper bound from the size of idxdoms.get(i)
                            ASTNode newlet = new Letting(range.getChild(1), BinOp.makeBinOp("+", range.getChild(0), NumberConstant.make(nValues-1)));
                            newlet = (new TransformSimplify()).transform(newlet);
                            newlettings.add(newlet);
                        }
                        
                    }
                }
            }
        }
        return newlettings;
    }
    
    public void correctIndicesConstantMatrix(String matname, boolean warning) {
        // Uses the method below to correct the indices of the matrix literal
        // to line up with the domain (that may have come from a given, and
        // therefore may be different to the domain in a letting or the index domains in the matrix literal).
        ASTNode mat = cm.get(matname).copy();    //  Copy here to avoid changing in-place a key in cm_names
        ASTNode dom = m.global_symbols.getDomain(matname);
        
        // fixIndicesConstantMatrix may change matrix in place so first remove it.
        removeEntry(matname);
        
        Pair<ASTNode, Boolean> p = fixIndicesConstantMatrix(dom, mat);
        
        if (p.getSecond() && warning) {
            CmdFlags.println("WARNING: Index domains do not match for the matrix " + matname);
            CmdFlags.println("WARNING: This could be a mismatch between the matrix given in the parameter file");
            CmdFlags.println("WARNING: and its matrix domain in the given statement in the model file.");
        }
        
        // Put it back, whether or not it has changed. 
        addEntry(matname, p.getFirst());
    }
    
    // Correct the indices in CMs to match a matrix domain.
    // For a constant matrix given in a parameter file, this is first
    // applied for the domain in the letting (if there is one).
    // Then it's applied a second time for the domain in the given.
    public static Pair<ASTNode, Boolean> fixIndicesConstantMatrix(ASTNode matdom, ASTNode mat) {
        // Returns a new constant matrix with fixed domains, and a boolean saying whether
        // any of the CM domains have in fact changed.
        // It also changes mat in place in some cases.
        // May also return null for the first return value when it is not possible to fit mat to matdom. 
        
        if (mat instanceof EmptyMatrix) {
            // Fix mat to align with matdom.
            ArrayList<ASTNode> matdomidx=matdom.getChildren(3);
            boolean ischanged = false;
            
            ArrayList<ASTNode> matidx=mat.getChild(0).getChildren(3);
            ASTNode matbasetype=mat.getChild(0).getChild(0);
            
            if( matidx.size() != matdomidx.size()) {
                // Number of dimensions do not match. 
                while(matidx.size() < matdomidx.size()) {
                    // Fill in extra empty dimensions.
                    matidx.add(new IntegerDomain(new EmptyRange()));
                }
                
                while(matidx.size() > matdomidx.size()) {
                    matidx.remove(matidx.size()-1);
                }
                ischanged=true;
            }
            
            for(int i=0; i<matdomidx.size(); i++) {
                if(matdomidx.get(i).isFiniteSet() && !matdomidx.get(i).equals(matidx.get(i))) {
                    matidx.set(i, matdomidx.get(i));
                    ischanged=true;
                }
            }
            
            if(ischanged) {
                return new Pair<ASTNode, Boolean>(new EmptyMatrix(new MatrixDomain(matbasetype, matidx)), true);
            }
            else {
                return new Pair<ASTNode, Boolean>(mat, false);
            }
        }
        else if(mat instanceof CompoundMatrix) {
            boolean ischanged = false;
            
            ASTNode cmindex = mat.getChild(0);
            ASTNode matdomindex = matdom.getChild(3);
            
            // matdomindex may be int(..), meaning irregular indexing. Only replace the compound matrix index if matdomindex is finite.
            
            if(matdomindex.isFiniteSet()) {
                if (! cmindex.getIntervalSet().equals(matdomindex.getIntervalSet())) {
                    mat.setChild(0, matdomindex);
                    ischanged = true;
                }
            }
            
            // Make a new matrix domain with one less index.
            ArrayList<ASTNode> inneridxdoms = matdom.getChildren(4);
            
            if (inneridxdoms.size() == 0) {
                return new Pair<ASTNode, Boolean>(mat, ischanged);
            }
            
            for (int i =1; i < mat.numChildren(); i++) {
                ASTNode innermatdom = new MatrixDomain(matdom.getChild(0), inneridxdoms);
                
                //  Recursive call.
                Pair<ASTNode, Boolean> p = fixIndicesConstantMatrix(innermatdom, mat.getChild(i));
                
                mat.setChild(i, p.getFirst());
                ischanged = ischanged || p.getSecond();
            }
            
            // In this branch mat has been changed in place.
            return new Pair<ASTNode, Boolean>(mat, ischanged);
        }
        else {
            // Number of dimensions of mat does not match matdom. 
            // Will be caught later in typechecking. 
            return new Pair<ASTNode, Boolean>(mat, false);
        }
    }
    
    // This is called as part of type checking to check
    // the dimensions and base domain of the constant matrices.
    public boolean typecheck() {
        for (String name : cm.keySet()) {
            ASTNode matdom = m.global_symbols.getDomain(name);
            ASTNode basedom = matdom.getChild(0);
            boolean boolMatrix = basedom.isBooleanSet();
            ArrayList<ASTNode> indexdoms = matdom.getChildren(3);
            
            if(cm.get(name).getDimension() != indexdoms.size()) {
                CmdFlags.println("ERROR: Number of dimensions differs for constant matrix: "+name);
                return false;
            }
            
            //  Retrieve the base domain as a set of intervals. 
            TransformSimplify ts = new TransformSimplify();
            ArrayList<Intpair> basedomset = ts.transform(basedom).getIntervalSet();
            
            if (!checkConstantMatrixDomain(name, cm.get(name), indexdoms, basedomset, boolMatrix, 0)) {
                return false;
            }
        }
        return true;
    }
    
    private boolean checkConstantMatrixDomain(String name, ASTNode mat, ArrayList<ASTNode> indexdoms, ArrayList<Intpair> basedom, boolean boolMatrix, int index) {
        ASTNode indexdom = indexdoms.get(index);
        // Check length of mat.
        TransformSimplify ts = new TransformSimplify();
        if (indexdom.isFiniteSet()) {
            long size = Intpair.numValues(ts.transform(indexdom).getIntervalSet());
            if (mat.numChildren() - 1 != size) {
                CmdFlags.println("ERROR: At index " + (index+1) + " of constant matrix " + name + ", actual size does not match the matrix dimensions.");
                return false;
            }
        }
        //  Any length is allowed if the index is int(..)
        
        if (index == indexdoms.size() - 1) {
            // Base case -- Check values are in the base domain
            for (int i =1; i < mat.numChildren(); i++) {
                ASTNode a = mat.getChild(i);
                if (! Intpair.contains(basedom, a.getValue())) {
                    CmdFlags.println("ERROR: Item " + a + " is not contained in domain of constant matrix " + name + ".");
                    return false;
                }
                if( boolMatrix && ! a.isRelation()) {
                    CmdFlags.println("ERROR: Item " + a + " is not boolean in constant matrix " + name + ".");
                    return false;
                }
            }
        }
        else {
            // Recursive case.
            for (int i =1; i < mat.numChildren(); i++) {
                ASTNode a = mat.getChild(i);
                if (!checkConstantMatrixDomain(name, a, indexdoms, basedom, boolMatrix, index + 1)) {
                    return false;
                }
            }
        }
        return true;
    }
    
    public ConstantMatrixStore copy(Model _m) {
        ConstantMatrixStore cp=new ConstantMatrixStore(_m);
        for (String name : cm.keySet()) {
            ASTNode matcp=cm.get(name).copy();
            cp.addEntry(name, matcp);
        }
        return cp;
    }
    
    public boolean equals(Object b) {
        if(!(b instanceof ConstantMatrixStore)) {
            return false;
        }
        ConstantMatrixStore c = (ConstantMatrixStore)b;
        return c.cm.equals(cm);
    }
    
    public int hashCode() {
        return cm.hashCode();
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Output methods
    
    public void toMinion(BufferedWriter b) throws IOException {
        // Output constant matrices.
        for (String name : cm.keySet()) {
            // skip already contained
            if (already_written.contains(name)){
                continue;
            }
            ArrayList<Long> dimensions = getConstantMatrixSize(cm.get(name));
            
            ArrayList<ASTNode> indexdomains=cm.get(name).getIndexDomainsIrregular();
            
            boolean regular=true;  // regular in all dimensions.
            boolean[] regulardim=new boolean[indexdomains.size()];    // regular per dimension.
            
            for(int i=0; i<indexdomains.size(); i++) {
                ArrayList<Intpair> a=indexdomains.get(i).getIntervalSet();
                regulardim[i]=!(a.size()==1 && a.get(0).lower==Long.MIN_VALUE && a.get(0).upper==Long.MAX_VALUE);
                regular=regular && regulardim[i];
            }
            
            // If two dimensional, print as tuplelist.
            if(dimensions.size() == 2 && regular) {
                b.append("**TUPLELIST**\n");
                b.append(name + " ");
                ASTNode a = cm.get(name);
                b.append(dimensions.get(0) + " " + dimensions.get(1) + "\n");
                for (int i =1; i < a.numChildren(); i++) {
                    ASTNode tuple = a.getChild(i);
                    if(tuple.isTuple()) {
                        for (int j=1; j <= tuple.getTupleLength(); j++) {
                            b.append(String.valueOf(tuple.getValueIdx(j)));
                            b.append(" ");
                        }
                    }
                    else {
                        assert tuple instanceof CompoundMatrix || tuple instanceof EmptyMatrix;
                        for (int j=1; j < tuple.numChildren(); j++) {
                            ASTNode element = tuple.getChild(j);
                            element.toMinion(b, false);
                            b.append(" ");
                        }
                    }
                    b.append("\n");
                }
            }
            
            // If three dimensional with size 2 in inner dimension, print as short tuple list.
            if(dimensions.size()==3 && dimensions.get(2)==2 && regulardim[2]) {
                b.append("**SHORTTUPLELIST**\n");
                b.append(name);
                b.append(" ");
                ASTNode cmat = cm.get(name);
                b.append(String.valueOf(cmat.numChildren()-1));
                b.append("\n");
                
                for(int i=1; i<cmat.numChildren(); i++) {
                    b.append("[");
                    ASTNode tup=cmat.getChild(i);
                    for(int j=1; j<cmat.getChild(i).numChildren(); j++) {
                        long var=tup.getChild(j).getChild(1).getValue();
                        long val=tup.getChild(j).getChild(2).getValue();
                        b.append("(");
                        b.append(String.valueOf(var-1));    //  Minion indexes variables from 0, SR from 1.
                        b.append(",");
                        b.append(String.valueOf(val));
                        b.append("),");
                    }
                    b.append("]\n");
                }
            }
            
            // Print as array of constants, in case there is a matrix deref
            // that is translated to element.
            // Minion won't accept a matrix with a dimension of size 0, or an irregular matrix.
            
            boolean zerodimension=false;
            for(int i=0; i<dimensions.size(); i++) {
                if(dimensions.get(i)==0) zerodimension=true;
            }
            
            if(!zerodimension && regular) {
                b.append("**VARIABLES**\n");
                b.append("ALIAS " + name + "[");
                for (int i =0; i < dimensions.size(); i++) {
                    b.append(String.valueOf(dimensions.get(i)));
                    if (i < dimensions.size() - 1) {
                        b.append(",");
                    }
                }
                
                b.append("]=");
                cm.get(name).toMinion(b, false);
                b.append("\n");
            }
            //add that we already wrote that.
            already_written.add(name);
        }
    }
    
    public void toFlatzinc(BufferedWriter b) throws IOException {
        // Constant matrices
        // look like this: array [1..10] of int: b =  [0, 0, 0, 0, 0, 0, 0, 0, 0, -50];
        for (String name : cm.keySet()) {
            ASTNode mat = cm.get(name);
            ArrayList<Long> dim = getConstantMatrixSize(mat);
            ArrayList<Long> cont = getConstantMatrixContents(mat);
            if (dim.size() == 1) {
                b.append("array [1.." + dim.get(0) + "] of int: " + name + " = " + cont.toString() + ";\n");
            }
        }
    }
    
    public void toMinizinc(StringBuilder b) {
        // Constant matrices
        // look like this: array [1..3] of int: b =  [1,2,3];
        for (String name : cm.keySet()) {
            ASTNode mat = cm.get(name);
            if(mat.isRegularMatrix()) {
                ///  Only regular constant matrices of dimension up to 2 are output to MiniZinc. 
                ArrayList<Long> dim = getConstantMatrixSize(mat);
                ArrayList<Long> cont = getConstantMatrixContents(mat);
                if (dim.size() == 1) {
                    b.append("array [1.." + dim.get(0) + "] of int: " + name + " = " + cont.toString() + ";\n");
                }
                else if(dim.size() == 2) {
                    b.append("array [1.." + dim.get(0) + ", 1.." + dim.get(1) + "] of int: " + name + " = ");
                    printMzn2darray(b, mat);
                    b.append(";\n");
                }
            }
        }
    }
    
    public static void printMzn2darray(StringBuilder b, ASTNode a) {
        assert a.getDimension()==2;
        b.append("[");
        for(int i=1; i<a.numChildren(); i++) {
            ASTNode ch=a.getChild(i);
            b.append("| ");
            for(int j=1; j<=ch.getTupleLength(); j++) {
                b.append(ch.getValueIdx(j));
                if(j< ch.getTupleLength()) b.append(",");
            }
        }
        b.append("|]");
    }
    
    public String toString() {
        StringBuilder sb=new StringBuilder();
        for (String name : cm.keySet()) {
            sb.append("letting "+name+" = "+cm.get(name)+"\n");
        }
        return sb.toString();
    }
}
