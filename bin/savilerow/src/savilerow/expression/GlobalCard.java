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

// Extended Global Cardinality Constraint
// Each child is a matrix.
// Implements the open semantics, i.e. values not mentioned in the value matrix are unconstrained, any number of them may occur.

public class GlobalCard extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public GlobalCard(ASTNode a, ASTNode b, ASTNode c) {
        super(a, b, c);
    }

    public ASTNode copy() {
        assert numChildren() == 3;
        return new GlobalCard(getChild(0), getChild(1), getChild(2));
    }

    public boolean isRelation() { return true; }
    
    //  The following is approximate.  If child 2 is not constants, then e.g. Minion will not get GAC. 
    @Override public boolean strongProp() {
	    return getChild(0).strongProp() && getChild(1).strongProp() && getChild(2).strongProp();
	}
    public boolean typecheck(SymbolTable st) {
        for (int i =0; i < 3; i++) {
            if (!getChild(i).typecheck(st)) {
                return false;
            }
            if (getChild(i).getDimension() != 1) {
                CmdFlags.println("ERROR: Expected one-dimensional matrix for each argument of gcc constraint: " + this);
                return false;
            }
        }
        if (getChild(1).getCategory() > ASTNode.Quantifier) {
            CmdFlags.println("ERROR: Expected no decision variables in second argument of gcc constraint: " + this);
            return false;
        }
        return true;
    }
    
    /// SHOULD reduce both target variables (throw out assigned) and values (throw out those that can't occur anywhere)
    @Override
    public ASTNode simplify() {
        ASTNode target=getChildConst(0);
        ASTNode values=getChildConst(1);
        ASTNode occs=getChildConst(2);
        
        if (values instanceof EmptyMatrix && occs instanceof EmptyMatrix) {
            return new BooleanConstant(true);
        }

        if (target.isMatrixLiteral() && values instanceof CompoundMatrix && occs instanceof CompoundMatrix) {
            ArrayList<ASTNode> ch = target.getChildren(1);
            ArrayList<ASTNode> vals = values.getChildren(1);
            ArrayList<ASTNode> cards = occs.getChildren(1);
            
            // Check bounds on cardinalities.
            long lowertotal=0;
            long uppertotal=0;
            for(int i=0; i<cards.size(); i++) {
                Intpair p=cards.get(i).getBounds();
                if(p.upper<0 || p.lower>ch.size()) {
                    return new BooleanConstant(false);
                }
                lowertotal+=p.lower;
                uppertotal+=p.upper;
            }
            
            if(lowertotal > ch.size()) {
                // More values required than target vars.
                return new BooleanConstant(false);
            }
            
            boolean changed = false;
            
            // Filter out any constants in the target variables
            for (int i =0; i < ch.size(); i++) {
                if (ch.get(i).isConstant()) {
                    for(int j=0; j<vals.size(); j++) {
                        if(vals.get(j).equals(ch.get(i))) {
                            cards.set(j, BinOp.makeBinOp("-", cards.get(j), NumberConstant.make(1L)));
                        }
                    }
                    
                    // remove the constant.
                    ch.remove(i);
                    i--;
                    changed = true;
                }
            }
            
            if (ch.size() == 0) {
                // No variables in target array.
                // Make each card expression equal to 0.
                ArrayList<ASTNode> newcts = new ArrayList<ASTNode>();
                for (int i =0; i < cards.size(); i++) {
                    newcts.add(new Equals(cards.get(i), NumberConstant.make(0)));
                }
                return new And(newcts);
            }
            
            if(changed) {
                if(target==getChild(0)) {
                    for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
                }
                if(values==getChild(1)) {
                    for(int i=0; i<vals.size(); i++) vals.get(i).setParent(null);
                }
                if(occs==getChild(2)) {
                    for(int i=0; i<cards.size(); i++) cards.get(i).setParent(null);
                }
                return new GlobalCard(CompoundMatrix.make(ch), CompoundMatrix.make(vals), CompoundMatrix.make(cards));
            }
        }
        return null;
    }
    @Override
    public ASTNode normalise() {
        // Just sort the target variables.  Later can co-sort values and occurrences
        if (getChild(0) instanceof CompoundMatrix) {
            ArrayList<ASTNode> ch = getChild(0).getChildren(1);
            boolean changed = sortByHashcode(ch);
            
            // Safe because ch must be non-empty
            if (changed) {
                for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
                getChild(1).setParent(null);
                getChild(2).setParent(null);
                return new GlobalCard(new CompoundMatrix(ch), getChild(1), getChild(2));
            }
        }
        return this;
    }
    
    @Override
    public ASTNode normaliseAlpha() {
        // Just sort the target variables.  Later can co-sort values and occurrences
        if (getChild(0) instanceof CompoundMatrix) {
            ArrayList<ASTNode> ch = getChild(0).getChildren(1);
            boolean changed = sortByAlpha(ch);
            
            // Safe because ch must be non-empty
            if (changed) {
                for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
                getChild(1).setParent(null);
                getChild(2).setParent(null);
                return new GlobalCard(new CompoundMatrix(ch), getChild(1), getChild(2));
            }
        }
        return null;
    }

    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        assert bool_context;
        b.append("gccweak(");
        getChild(0).toMinion(b, false);
        b.append(",");
        getChild(1).toMinion(b, false);
        b.append(",");
        getChild(2).toMinion(b, false);
        b.append(")");
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        if(CmdFlags.getGecodetrans()) {
            b.append("constraint gecode_global_cardinality(");  //  Different name in Gecode
        }
        else {
            b.append("constraint global_cardinality(");
        }
        getChild(0).toFlatzinc(b, false);
        b.append(",");
        getChild(1).toFlatzinc(b, false);
        b.append(",");
        getChild(2).toFlatzinc(b, false);
        b.append(")::domain;");
    }
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("global_cardinality(");
        getChild(0).toMinizinc(b, false);
        b.append(",");
        getChild(1).toMinizinc(b, false);
        b.append(",");
        getChild(2).toMinizinc(b, false);
        b.append(")");
    }
    public String toString() {
        return "gcc(" + getChild(0) + "," + getChild(1) + "," + getChild(2) + ")";
    }

    public void toJSON(StringBuilder bf) {
        toAlternateJSON(this, bf);
    }

    public static void toAlternateJSON(ASTNode node, StringBuilder bf) {
        node.toJSONHeader(bf, true);
        bf.append("\"children\": [\n");
        // variables
        node.getChild(0).toJSON(bf);
        bf.append(",\n");

        // encapsulate second and third lists into list of pairs
        ASTNode matrix2 = node.getChildConst(1);
        ASTNode matrix3 = node.getChildConst(2);
        int numVals = matrix2.numChildren();
        bf.append("{\n\"type\": \"pairList\",\n");        // open object declaration
        bf.append("\"symmetricChildren\": true,\n");
        bf.append("\"children\": [");

        // matrix2 and 3 as pairs
        for (int i = 1; i < numVals; i++) {
            bf.append("\n{\n\"type\": \"pair\",\n\"symmetricChildren\": false,\n");            // opening pair object
            bf.append("\"children\": [\n");
            matrix2.getChild(i).toJSON(bf);
            bf.append(",\n");
            matrix3.getChild(i).toJSON(bf);
            bf.append("]\n}");
            
            // add comma if necessary
            if (i < numVals - 1) {
                bf.append(",");
            }
        }
        bf.append("]\n}]}");
    }
    
    public boolean isChildSymmetric(int childIndex) {
        return childIndex == 0;        // first child is symmetric
    }
}
