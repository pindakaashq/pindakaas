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
import java.util.Arrays;

import savilerow.CmdFlags;
import savilerow.model.SMT;

public class CompoundMatrixInt1D extends ASTNode {
    public static final long serialVersionUID = 1L;
    
    public int[] values;
    
    // One-dimensional matrix of signed integers, indexed from 1 contiguously. 
    public CompoundMatrixInt1D(int[] mat) {
        super();
        values=mat;
    }
    
    @Override public boolean strongProp() {
        return true;
	}
	
    public boolean isNumerical() {
        return true;
    }
    
    public ASTNode copy() {
        return new CompoundMatrixInt1D(values);  //  Assumes the array can be re-used; will never be changed. 
    }
    
    @Override
    public boolean equals(Object b) {
        if (! (b instanceof CompoundMatrixInt1D)) {
            return false;
        }
        return Arrays.equals(values, ((CompoundMatrixInt1D)b).values);
    }
    @Override
    public int hashCode() {
        return Arrays.hashCode(values);
    }
    
    public boolean toFlatten(boolean propagate) { return false; }
    
    public Intpair getBounds() {
        int lower=values[0];
        int upper=values[0];
        for (int i=1; i < values.length; i++) {
            int tmp=values[i];
            if(tmp<lower) lower=tmp;
            if(tmp>upper) upper=tmp;
        }
        return new Intpair(lower,upper);
    }
    
    public ArrayList<Intpair> getIntervalSetExp() {
        ArrayList<Intpair> a=new ArrayList<>();
        for(int i=0; i<values.length; i++) {
            a.add(new Intpair(values[i], values[i]));
        }
        Intpair.normalise(a);
        return a;
    }
    
    // Assumes the dimension is the same everywhere.
    public int getDimension() {
        return 1;
    }
    
    @Override
    public boolean isRegularMatrix() {
        return true;
    }
    
    // For a regular matrix literal only, get the index domains.
    public ArrayList<ASTNode> getIndexDomains() {
        ArrayList<ASTNode> tmp = new ArrayList<ASTNode>();
        tmp.add(new IntegerDomainConcrete(1, values.length));
        return tmp;
    }
    
    // Much slower version for irregular matrices.
    public ArrayList<ASTNode> getIndexDomainsIrregular() {
        ArrayList<ASTNode> tmp = new ArrayList<ASTNode>();
        tmp.add(new IntegerDomainConcrete(1, values.length));
        return tmp;
    }
    
    @Override public boolean isMatrixLiteral() {
        return true;
    }
    
    //  Provides a common interface with CompoundMatrix for retrieving elements. 
    //  Indexes from 1. 
    public boolean isTuple() {
        return true;
    }
    public int getTupleLength() {
        return values.length;
    }
    public long getValueIdx(int idx) {
        return (long) values[idx-1];
    }
    
    // ALL output methods except E' drop the index.
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        assert !bool_context;
        b.append("[");
        for (int i=0; i < values.length; i++) {
            b.append(String.valueOf(values[i]));
            if (i < values.length - 1) {
                b.append(", ");
            }
        }
        b.append("]");
    }
    
    public String toString() {
        StringBuilder st = new StringBuilder();
        st.append("[");
        for (int i=0; i < values.length; i++) {
            st.append(values[i]);
            if (i < values.length - 1) {
                st.append(", ");
            }
        }
        st.append("]");
        return st.toString();
    }
    
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("[");
        for (int i=0; i < values.length; i++) {
            b.append(String.valueOf(values[i]));
            if (i < values.length - 1) {
                b.append(", ");
            }
        }
        b.append("]");
    }

    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("[");
        for (int i=0; i < values.length; i++) {
            b.append(values[i]);
            if (i < values.length - 1) {
                b.append(", ");
            }
        }
        b.append("]");
    }
    
    public void toJSON(StringBuilder bf) {
        toJSONHeader(bf, true);
        // children
        bf.append("\"Domain\":");
        (new IntegerDomainConcrete(1, values.length)).toJSON(bf);
        bf.append(",\n");
        bf.append("\"Children\": [");
        for (int i=0; i < values.length; i++) {
            bf.append("\n");
            bf.append(values[i]+"\n");
            // not last child
            if (i < values.length - 1) {
                bf.append(",");
            }
        }
        bf.append("]\n}");
    }

    public String smtEncodeInt(SMT satModel) {
        String s = "";
        
        for (int i=0; i < values.length; i++) {
            s += SMT.toSMTInt(Long.valueOf(values[i]));
            if(i<values.length-1) {
                s += " ";
            }
        }
        
        return s;
    }
    
    public String smtEncodeBV(SMT satModel) {
        String s = "";
        
        for (int i=0; i < values.length; i++) {
            s += SMT.toSMTBV(Long.valueOf(values[i]));
            if(i<values.length-1) {
                s += " ";
            }
        }
        
        return s;
    }
    
    public boolean childrenAreSymmetric() {
        return getParent().isChildSymmetric(getChildNo());
    }
    
    public boolean usesSMTEncoding() { return CmdFlags.getUseBV() || CmdFlags.getUseNIA() || CmdFlags.getUseLIA() || CmdFlags.getUseIDL(); }
}
