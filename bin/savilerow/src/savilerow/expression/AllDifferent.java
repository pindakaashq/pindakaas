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

import savilerow.*;
import savilerow.model.*;

// One child, a matrix type

public class AllDifferent extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public AllDifferent(ASTNode r) {
        super(r);
    }

    // Ctor for a binary disequality.
    public AllDifferent(ASTNode a, ASTNode b) {
        super(CompoundMatrix.make(a,b));
    }

    public ASTNode copy() {
        return new AllDifferent(getChild(0));
    }

    public boolean isRelation() { return true; }

    public boolean typecheck(SymbolTable st) {
        if (!getChild(0).typecheck(st)) {
            return false;
        }
        if (getChild(0).getDimension() != 1) {
            CmdFlags.println("ERROR: Expected one-dimensional matrix in allDiff constraint: " + this);
            return false;
        }
        return true;
    }
    public ASTNode simplify() {
        ASTNode ch = getChildConst(0);
        if (ch instanceof EmptyMatrix) {
            return new BooleanConstant(true);
        }
        if (ch instanceof CompoundMatrix) {
            for (int i =1; i < ch.numChildren(); i++) {
                for (int j = i + 1; j < ch.numChildren(); j++) {
                    if (ch.getChild(i).equals(ch.getChild(j))) {
                        return new BooleanConstant(false);                        // symbolic equality of two items.
                    }

                    if (ch.getChild(i).isConstant() && ch.getChild(j).isConstant() && ch.getChild(i).getValue() == ch.getChild(j).getValue()) {
                        return new BooleanConstant(false);                        // numerical equality of two items, both constants. e.g. false=0.
                    }
                }
            }
            
            if (ch.numChildren() < 3) {
                return new BooleanConstant(true);
            }
            // One or zero elements are always pairwise different.
            if(ch.getCategory()==ASTNode.Constant) {
                //  We have checked for pairwise equality so we now know the constraint is satisfied.
                //  Constant matrices retrieved from cmstore can't get past here.
                return new BooleanConstant(true);
            }
            
            //  Contains only two Booleans. Convert into a logical comparison 
            if(ch.numChildren()==3 && ch.getChild(1).isRelation() && ch.getChild(2).isRelation()) {
                return new Negate(new Iff(ch.getChild(1), ch.getChild(2)));
            }
            
            // Filter out any constants that are not within the bounds of any other element in the alldiff.
            ArrayList<ASTNode> items = ch.getChildren(1);
            boolean changed = false;
            
            for (int i =0; i < items.size(); i++) {
                if (items.get(i).isConstant()) {
                    boolean intersects = false;                    // does item i intersect with any other.
                    long val = items.get(i).getValue();

                    for (int j =0; j < items.size(); j++) {
                        if (i != j) {
                            Intpair p = items.get(j).getBounds();

                            if (val >= p.lower && val <= p.upper) {

                                if (items.get(j) instanceof Identifier) {
                                    // Get the full domain.
                                    ASTNode dom = ((Identifier) items.get(j)).getDomain();

                                    if(dom.isConstantSet()) {
                                        if (dom.containsValue(val)) {
                                            intersects = true;
                                            break;
                                        }
                                        else {
                                            continue;                                            // Does not intersect.
                                        }
                                    }
                                    // Only bounds are available -- fall through.
                                }

                                // Only the bounds are available.
                                intersects = true;
                                break;
                            }
                        }
                    }

                    if (!intersects) {
                        // remove i from the alldiff.
                        items.remove(i);
                        i--;
                        changed = true;
                    }
                }
            }
            
            if (changed) {
                for(int i=0; i<items.size(); i++) items.get(i).setParent(null);  // Do not copy.
                return new AllDifferent(CompoundMatrix.make(items));
            }
            
            // Disequality between ch1 and ch2.
            // Should do every simplification equality would do.
            // Allow aggregation to be done first, to allow binary != to be collected before
            // any changes are made. 
            if(ch.numChildren()==3 && CmdFlags.getAfterAggregate()) {
                ASTNode ch1=ch.getChild(1);
                ASTNode ch2=ch.getChild(2);
                // Already checked for symbolic and numeric equality.
                
                Intpair b0=ch1.getBounds();
                Intpair b1=ch2.getBounds();
                
                if(b0.lower>b1.upper) {
                    return new BooleanConstant(true);  // lower bound of c1 is greater than upper bound of c2.
                }
                if(b0.upper<b1.lower) {
                    return new BooleanConstant(true);  // upper bound of c1 is less than lower bound of c2.
                }
                
                // Already checked constants against domains of variables.
                
                // If both sides sums, move to one side to allow simplification.
                if(ch1 instanceof WeightedSum && ch2 instanceof WeightedSum) {
                    ch1.setParent(null);
                    ch2.setParent(null);
                    return new AllDifferent(CompoundMatrix.make(BinOp.makeBinOp("-", ch1, ch2), NumberConstant.make(0)));
                }
                
                // It helps identical CSE if sums have no constants in them. 
                // Shift the constant to the other side to combine with constant/param/quantifier id. 
                if(ch1 instanceof WeightedSum && ch1.getCategory()==ASTNode.Decision && ch2.getCategory()<ASTNode.Decision) {
                    Pair<ASTNode, ASTNode> p1=((WeightedSum)ch1).retrieveConstant();
                    if(p1!=null) {
                        ch2.setParent(null);
                        return new AllDifferent(CompoundMatrix.make(p1.getSecond(), BinOp.makeBinOp("-", ch2, p1.getFirst())));
                    }
                }
                if(ch2 instanceof WeightedSum && ch2.getCategory()==ASTNode.Decision && ch1.getCategory()<ASTNode.Decision) {
                    Pair<ASTNode, ASTNode> p1=((WeightedSum)ch2).retrieveConstant();
                    if(p1!=null) {
                        ch1.setParent(null);
                        return new AllDifferent(CompoundMatrix.make(p1.getSecond(), BinOp.makeBinOp("-", ch1, p1.getFirst())));
                    }
                }
                
                // Factor out the GCD of a sum.
                if(ch1 instanceof WeightedSum && ch2.isConstant()) {
                    Pair<ASTNode, ASTNode> p=((WeightedSum)ch1).factorOutGCD();
                    
                    if(p!=null) {
                        long gcd=p.getFirst().getValue();
                        long c=ch2.getValue();
                        
                        long rhs=Divide.div(c, gcd);
                        if(rhs*gcd != c) {
                            return new BooleanConstant(true);   // Some rounding occurred so two sides cannot be equal.
                        }
                        else {
                            return new AllDifferent(CompoundMatrix.make(p.getSecond(), NumberConstant.make(rhs)));
                        }
                    }
                }
                if(ch2 instanceof WeightedSum && ch1.isConstant()) {
                    Pair<ASTNode, ASTNode> p=((WeightedSum)ch2).factorOutGCD();
                    
                    if(p!=null) {
                        long gcd=p.getFirst().getValue();
                        long c=ch1.getValue();
                        
                        long rhs=Divide.div(c, gcd);
                        if(rhs*gcd != c) {
                            return new BooleanConstant(true);   // Some rounding occurred so two sides cannot be equal.
                        }
                        else {
                            return new AllDifferent(CompoundMatrix.make(p.getSecond(), NumberConstant.make(rhs)));
                        }
                    }
                }
                
                // Constants have been removed from sums by the above. Catch x-y!=0 and
                // rearrange to x!=y.
                if(ch1 instanceof WeightedSum && ch1.numChildren()==2 && ch2.isConstant() && ch2.getValue()==0) {
                    long wt1=((WeightedSum)ch1).getWeight(0);
                    long wt2=((WeightedSum)ch1).getWeight(1);
                    if(wt1+wt2==0) {
                        ch1.getChild(0).setParent(null);
                        ch1.getChild(1).setParent(null);
                        return new AllDifferent(CompoundMatrix.make(ch1.getChild(0), ch1.getChild(1)));
                    }
                }
                if(ch2 instanceof WeightedSum && ch2.numChildren()==2 && ch1.isConstant() && ch1.getValue()==0) {
                    long wt1=((WeightedSum)ch2).getWeight(0);
                    long wt2=((WeightedSum)ch2).getWeight(1);
                    if(wt1+wt2==0) {
                        ch2.getChild(0).setParent(null);
                        ch2.getChild(1).setParent(null);
                        return new AllDifferent(CompoundMatrix.make(ch2.getChild(0), ch2.getChild(1)));
                    }
                }
            }
        }
        return null;
    }

    @Override
    public boolean isNegatable() {
        return getChild(0) instanceof CompoundMatrix && getChild(0).numChildren() == 3;
    }
    @Override
    public ASTNode negation() {
        assert getChild(0) instanceof CompoundMatrix && getChild(0).numChildren() == 3;
        return new Equals(getChild(0).getChild(1), getChild(0).getChild(2));
    }

    public ASTNode normalise() {
        // sort by hashcode
        if (!(getChild(0) instanceof CompoundMatrix)) {
            return this;
        }
        
        ArrayList<ASTNode> ch = getChild(0).getChildren(1);
        
        boolean changed = sortByHashcode(ch);
        if (changed) {
            for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
            return new AllDifferent(new CompoundMatrix(ch));
        } else {
            return this;
        }
    }
    
    public ASTNode normaliseAlpha() {
        // sort alphabetically
        if (!(getChild(0) instanceof CompoundMatrix)) {
            return null;
        }
        
        ArrayList<ASTNode> ch = getChild(0).getChildren(1);
        
        boolean changed = sortByAlpha(ch);
        if (changed) {
            for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
            return new AllDifferent(new CompoundMatrix(ch));
        } else {
            return null;
        }
    }
    
    public boolean strongProp() {
        return getChild(0).strongProp();  //  In many constraint solvers we will get GAC on alldiff.
    }
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        assert bool_context;
        assert numChildren() == 1;
        ASTNode ch = getChild(0);
        if (ch instanceof CompoundMatrix && ch.numChildren() == 3) {
            b.append("diseq(");
            ch.getChild(1).toMinion(b, false);
            b.append(",");
            ch.getChild(2).toMinion(b, false);
            b.append(")");
        } else {
            String ctname = "gacalldiff";
            if (ch instanceof CompoundMatrix) {
                for (int i =1; i < ch.numChildren(); i++) {
                    if (CmdFlags.getUseBoundVars() && ch.getChild(i).exceedsBoundThreshold()) {
                        ctname = "alldiff";
                        break;
                    }
                }
            }

            b.append(ctname);
            b.append("(");
            getChild(0).toMinion(b, false);
            b.append(")");
        }
    }
    public String toString() {
        if (getChild(0) instanceof CompoundMatrix && getChild(0).numChildren() == 3) {
            return "(" + getChild(0).getChild(1) + " != " + getChild(0).getChild(2) + ")";
        }
        return "allDiff(" + getChild(0) + ")";
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        assert numChildren() == 1;
        ASTNode ch = getChild(0);
        if (ch instanceof CompoundMatrix && ch.numChildren() == 3) {
            b.append("constraint int_ne(");            /// This case will work with reification
            ch.getChild(1).toFlatzinc(b, false);
            b.append(",");
            ch.getChild(2).toFlatzinc(b, false);
            b.append(");");
        } else {
            if(CmdFlags.getOrtoolstrans() || CmdFlags.getChuffedtrans()) {
                b.append("constraint fzn_all_different_int(");
            }
            else {
                b.append("constraint all_different_int(");
            }
            getChild(0).toFlatzinc(b, false);
            b.append(")::domain;");
        }
    }
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        ASTNode ch = getChild(0);
        if (ch instanceof CompoundMatrix && ch.numChildren() == 3) {
            b.append("(");
            ch.getChild(1).toMinizinc(b, false);
            b.append("!=");
            ch.getChild(2).toMinizinc(b, false);
            b.append(")");
        } else {
            b.append("all_different(");
            getChild(0).toMinizinc(b, false);
            b.append(")");
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   SAT encoding of binary not-equal only. Longer AllDifferents should be
    //   decomposed before output. 
    
    public Long toSATLiteral(Sat satModel) {
        assert getChild(0).numChildren()==3;
        ASTNode ch0=getChild(0).getChild(1);
        ASTNode ch1=getChild(0).getChild(2);
        
	    if(ch0.isConstant()) {
	        return -ch1.directEncode(satModel, ch0.getValue());
        }
        if(ch1.isConstant()) {
            return -ch0.directEncode(satModel, ch1.getValue());
        }
        return null;
	}
    
    public void toSAT(Sat satModel) throws IOException
    {
        assert getChild(0).numChildren()==3;
        //  Direct encoding of pairwise not-equal constraints.
        ASTNode ch = getChild(0);
        for (int i=1; i < ch.numChildren(); i++) {
            for (int j=i+1; j<ch.numChildren(); j++) {
                //satModel.supportEncodingBinary(this, ch.getChild(i), ch.getChild(j));
                satModel.directEncoding(this, ch.getChild(i), ch.getChild(j));
            }
        }
    }
    
    public void toSATWithAuxVar(Sat satModel, long reifyVar) throws IOException {
        assert getChild(0).numChildren()==3;
        
        new Equals(getChild(0).getChild(1), getChild(0).getChild(2)).toSATWithAuxVar(satModel, -reifyVar);
    }
    
    //   Test function represents binary not-equals
    public boolean test(long val1, long val2) {
        return val1!=val2;
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //  JSON output for symmetry detection
    
    public void toJSON(StringBuilder bf) {
        toJSONHeader(bf, true);
        // children
        bf.append("\"Children\": [");
        if(getChild(0) instanceof CompoundMatrix && getChild(0).numChildren()==3) {
            //   Special case for binary != constraint.
            getChild(0).getChild(1).toJSON(bf);
            bf.append(", ");
            getChild(0).getChild(2).toJSON(bf);
        }
        else {
            // Same as toJSON method in ASTNode.
            for (int i = 0; i < numChildren(); i++) {
                bf.append("\n");
                getChild(i).toJSON(bf);
                // not last child
                if (i < numChildren() - 1) {
                    bf.append(",");
                }
            }
        }
        bf.append("]\n}");
    }
    
    public boolean usesSMTEncoding() {
        if (getChild(0) instanceof CompoundMatrix && getChild(0).numChildren() == 3) {
            return true;
        }
        return !CmdFlags.SMTDecompAlldiff();
    }
    
    public void toSMT(SMT satModel) throws IOException {
        satModel.addSMTClause(smtEncodeBool(satModel));
    }

    public String smtEncodeBool(SMT satModel) {
        String s = "(distinct";
        
        for(ASTNode ch : getChildren()) {
            if (CmdFlags.getUseBV()) {
                s += " " + ch.smtEncodeBV(satModel);
            }
            else {
                s += " " + ch.smtEncodeInt(satModel);
            }
        }
        
        return s + ")";
    }
    
    @Override
    public String smtEncodeBV(SMT satModel) {
        return "(ite " + this.smtEncodeBool(satModel) + " " + SMT.toSMTBV(1) + " " + SMT.toSMTBV(0) + ")";
    }

    @Override
    public String smtEncodeInt(SMT satModel) {
        return "(ite " + smtEncodeBool(satModel) + " 1 0)";
    }

    public boolean childrenAreSymmetric() {
        return (getChild(0) instanceof CompoundMatrix && getChild(0).numChildren()==3);
    }
    
    public boolean isChildSymmetric(int childIndex) {
        // If not a binary != ct, then the matrix inside should be regarded as symmetric.
        return !(getChild(0) instanceof CompoundMatrix && getChild(0).numChildren()==3);
    }

    public boolean canChildBeConvertedToDifference(int childIndex) {
        return isMyOnlyOtherSiblingEqualZero(childIndex);
    }

}
