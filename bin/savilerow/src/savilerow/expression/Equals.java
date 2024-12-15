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
import savilerow.treetransformer.TransformSimplify;

// Equality between two variables or a variable and a constant (two constants would be simplified to true or false).
// Cannot represent reification or ternary numerical constraint -- see ToVariable. 

public class Equals extends BinOp
{
    public static final long serialVersionUID = 1L;
    public Equals(ASTNode l, ASTNode r) {
        super(l, r);
    }
    
    public ASTNode copy() {
        return new Equals(getChild(0), getChild(1));
    }
    public boolean isRelation(){return true;}
    public boolean strongProp() {
        return getChild(0).strongProp() && getChild(1).strongProp();
    }
    
    public boolean typecheck(SymbolTable st) {
        if(!super.typecheck(st)) {
            return false;
        }
        for(int i=0; i<2; i++) {
            if(getChild(i) instanceof Less || getChild(i) instanceof LessEqual || getChild(i) instanceof Equals || getChild(i) instanceof NotEqual) {
                CmdFlags.println("ERROR: Nested non-associative operators: "+this);
                CmdFlags.println("ERROR: Add brackets to remove ambiguity.");
                return false;
            }
        }
        return true;
    }
    
    public ASTNode simplify() {
        if(getChild(0).equals(getChild(1))) {  // If symbolically equal, return true.
            return new BooleanConstant(true);
        }
        
        // Simplify to <-> if both sides are boolean.
        if(getChild(0).isRelation() && getChild(1).isRelation()) {
            return new Iff(getChild(0), getChild(1));
        }
        
        // Simplify away UnaryMinus if possible.
        if(getChild(0) instanceof UnaryMinus && getChild(1).isConstant()) {
            return new Equals(getChild(0).getChild(0), NumberConstant.make(-getChild(1).getValue()));
        }
        if(getChild(1) instanceof UnaryMinus && getChild(0).isConstant()) {
            return new Equals(getChild(1).getChild(0), NumberConstant.make(-getChild(0).getValue()));
        }
        
        if(getChild(0).isConstant() && getChild(1).isConstant()) {
            // If equal when interpreted as integer.... (includes 1=true)
            return new BooleanConstant( getChild(0).getValue() == getChild(1).getValue() );
        }
        
        Intpair b0=getChild(0).getBounds();
        Intpair b1=getChild(1).getBounds();
        
        if(b0.lower>b1.upper || b0.upper<b1.lower) {
            return new BooleanConstant(false);  // bounds do not overlap.
        }
        
        // If one child is a variable and the other a constant, first check domain of variable for the constant.
        // Then deal with boolean case. 
        ASTNode a=getChild(0);
        ASTNode b=getChild(1);
        if(b instanceof Identifier) {  // swap.
            a=b;
            b=getChild(0);
        }
        
        if(a instanceof Identifier && b.isConstant()) {
            ASTNode domain=((Identifier)a).getDomain();
            if(domain.getCategory() == ASTNode.Constant) {
                TransformSimplify ts=new TransformSimplify();
                domain=ts.transform(domain);
                if(! domain.containsValue(b.getValue())) {
                    return new BooleanConstant(false);
                }
            }
            
            if(a.isRelation()) {
                // Boolean case -- can simplify to a or !a. 
                long bval=b.getValue();
                if(bval==0) {
                    return new Negate(a);
                }
                else if(bval==1) {
                    return a;
                }
            }
        }
        
        // Now simplify sum1=sum2 to sum1-sum2=0
        if(getChild(0) instanceof WeightedSum && getChild(1) instanceof WeightedSum) {
            this.detachChildren();
            return new Equals(BinOp.makeBinOp("-", getChild(0), getChild(1)), NumberConstant.make(0));
        }
        
        // It helps identical CSE if sums have no constants in them. 
        // Shift the constant to the other side to combine with constant/param/quantifier id. 
        if(getChild(0) instanceof WeightedSum && getChild(0).getCategory()==ASTNode.Decision && getChild(1).getCategory()<ASTNode.Decision) {
            Pair<ASTNode, ASTNode> p1=((WeightedSum)getChild(0)).retrieveConstant();
            if(p1!=null) {
                getChild(1).setParent(null);
                return new Equals(p1.getSecond(), BinOp.makeBinOp("-", getChild(1), p1.getFirst()));
            }
        }
        if(getChild(1) instanceof WeightedSum && getChild(1).getCategory()==ASTNode.Decision && getChild(0).getCategory()<ASTNode.Decision) {
            Pair<ASTNode, ASTNode> p1=((WeightedSum)getChild(1)).retrieveConstant();
            if(p1!=null) {
                getChild(0).setParent(null);
                return new Equals(BinOp.makeBinOp("-", getChild(0), p1.getFirst()), p1.getSecond());
            }
        }
        
        // Factor out the GCD of a sum.
        if(getChild(0) instanceof WeightedSum && getChild(1).isConstant()) {
            Pair<ASTNode, ASTNode> p=((WeightedSum)getChild(0)).factorOutGCD();
            
            if(p!=null) {
                long gcd=p.getFirst().getValue();
                long c=getChild(1).getValue();
                
                if(c%gcd != 0) {
                    // If there is a remainder when dividing the RHS by the GCD, then the sum= cannot be satisfied (RHS will be fractional)
                    return new BooleanConstant(false);
                }
                
                return new Equals(p.getSecond(), NumberConstant.make(c/gcd));
            }
        }
        if(getChild(1) instanceof WeightedSum && getChild(0).isConstant()) {
            Pair<ASTNode, ASTNode> p=((WeightedSum)getChild(1)).factorOutGCD();
            
            if(p!=null) {
                long gcd=p.getFirst().getValue();
                long c=getChild(0).getValue();
                
                if(c%gcd != 0) {
                    // If there is a remainder when dividing the LHS by the GCD, then the sum= cannot be satisfied (RHS will be fractional)
                    return new BooleanConstant(false);
                }
                
                return new Equals(p.getSecond(), NumberConstant.make(c/gcd));
            }
        }
        
        // Constants have been removed from sums by the above. Catch x-y=0 and
        // rearrange to x=y.
        if(getChild(0) instanceof WeightedSum && getChild(0).numChildren()==2 && getChild(1).isConstant() && getChild(1).getValue()==0) {
            long wt1=((WeightedSum)getChild(0)).getWeight(0);
            long wt2=((WeightedSum)getChild(0)).getWeight(1);
            if(wt1+wt2==0) {
                getChild(0).detachChildren();
                return new Equals(getChild(0).getChild(0), getChild(0).getChild(1));
            }
        }
        if(getChild(1) instanceof WeightedSum && getChild(1).numChildren()==2 && getChild(0).isConstant() && getChild(0).getValue()==0) {
            long wt1=((WeightedSum)getChild(1)).getWeight(0);
            long wt2=((WeightedSum)getChild(1)).getWeight(1);
            if(wt1+wt2==0) {
                getChild(1).detachChildren();
                return new Equals(getChild(1).getChild(0), getChild(1).getChild(1));
            }
        }
        
        //  Equality of a constant with an element constraint containing a constant matrix -- becomes an InSet constraint.
        if(getChild(0).isConstant() && getChild(1) instanceof ElementOne && getChild(1).getChild(0).getCategory()==ASTNode.Constant) {
            ArrayList<Intpair> set=new ArrayList<Intpair>();
            for(int i=1; i<getChild(1).getChild(0).numChildren(); i++) {
                if(getChild(0).getValue()==getChild(1).getChild(0).getChild(i).getValue()) {
                    set.add(new Intpair(i, i));
                }
            }
            return new InSet(getChild(1).getChild(1), Intpair.makeDomain(set, false));
        }
        if(getChild(1).isConstant() && getChild(0) instanceof ElementOne && getChild(0).getChild(0).getCategory()==ASTNode.Constant) {
            ArrayList<Intpair> set=new ArrayList<Intpair>();
            for(int i=1; i<getChild(0).getChild(0).numChildren(); i++) {
                if(getChild(1).getValue()==getChild(0).getChild(0).getChild(i).getValue()) {
                    set.add(new Intpair(i, i));
                }
            }
            return new InSet(getChild(0).getChild(1), Intpair.makeDomain(set, false));
        }
        
        return null;
    }
    
    @Override
    public boolean isNegatable() {
        return true;
    }
    @Override
    public ASTNode negation() {
        return new AllDifferent(getChild(0), getChild(1));
    }
    
    @Override
    public ASTNode normalise() {
        if(getChild(0).hashCode()>getChild(1).hashCode()) {
            detachChildren();
            return new Equals(getChild(1), getChild(0));
        }
        return this;
    }
    
    @Override
    public ASTNode normaliseAlpha() {
        if(getChild(0).toString().compareTo(getChild(1).toString())>0) {
            detachChildren();
            return new Equals(getChild(1), getChild(0));
        }
        return null;
    }
    
    public String toString() {
        return "("+getChild(0)+"="+getChild(1)+")";
    }
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
    {
        assert bool_context;
        if(getChild(0).isConstant()) {
            if(CmdFlags.getUseBoundVars() && getChild(1).exceedsBoundThreshold() ) {
                b.append("eq(");
            }
            else {
                b.append("w-literal(");
            }
            getChild(1).toMinion(b, false);
            b.append(",");
            getChild(0).toMinion(b, false);
            b.append(")");
        }
        else if(getChild(1).isConstant()) {
            if(CmdFlags.getUseBoundVars() && getChild(0).exceedsBoundThreshold() ) {
                b.append("eq(");
            }
            else {
                b.append("w-literal(");
            }
            getChild(0).toMinion(b, false);
            b.append(",");
            getChild(1).toMinion(b, false);
            b.append(")");
        }
        else {
            if(CmdFlags.getUseBoundVars() && ( getChild(0).exceedsBoundThreshold() || getChild(1).exceedsBoundThreshold() )) {
                b.append("eq(");
            }
            else {
                b.append("gaceq(");
            }
            getChild(0).toMinion(b, false);
            b.append(",");
            getChild(1).toMinion(b, false);
            b.append(")");
        }
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("constraint int_eq(");
        getChild(0).toFlatzinc(b, false);
        b.append(",");
        getChild(1).toFlatzinc(b, false);
        b.append(");");
    }
    
    // Might be a problem here.. what if it contains a bool type.
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("(");
        getChild(0).toMinizinc(b, false);
        b.append("==");
        getChild(1).toMinizinc(b, false);
        b.append(")");
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //  SAT encoding
    
    public Long toSATLiteral(Sat satModel) {
        if(getChild(0).isConstant()) {
            return getChild(1).directEncode(satModel, getChild(0).getValue());
        }
        if(getChild(1).isConstant()) {
            return getChild(0).directEncode(satModel, getChild(1).getValue());
        }
        return null;
    }
    
    public void toSAT(Sat satModel) throws IOException {
        // Support encoding just for equality. 
        // [x!=a] \/ [y=a] for all a,  and both ways round (x and y). 
        encodeEquality(satModel, false, 0);
    }
    
    public void toSATWithAuxVar(Sat satModel, long aux) throws IOException {
        encodeEquality(satModel, true, aux);
        
        // Direct encode of the inverse constraint.
        ArrayList<Intpair> domain1=getChild(0).getIntervalSetExp();
        ArrayList<Intpair> domain2=getChild(1).getIntervalSetExp();
        
        for (Intpair pair1 : domain1)
        {
            for (long i=pair1.lower; i<=pair1.upper; i++)
            {
                satModel.addClause(-getChild(0).directEncode(satModel, i), -getChild(1).directEncode(satModel, i), aux);
            }
        }
    }
    
    private void encodeEquality(Sat satModel, boolean auxused, long aux) throws IOException {
        //  aux ->  var1 = var2
        ArrayList<Intpair> domain1=getChild(0).getIntervalSetExp();
        ArrayList<Intpair> domain2=getChild(1).getIntervalSetExp();
        
        for (Intpair pair1 : domain1)
        {
            for (long i=pair1.lower; i<=pair1.upper; i++)
            {
                if(auxused) {
                    satModel.addClause(-getChild(0).directEncode(satModel, i), getChild(1).directEncode(satModel, i), -aux);
                }
                else {
                    satModel.addClause(-getChild(0).directEncode(satModel, i), getChild(1).directEncode(satModel, i));
                }
            }
        }
        
        for (Intpair pair1 : domain2)
        {
            for (long i=pair1.lower; i<=pair1.upper; i++)
            {
                if(auxused) {
                    satModel.addClause(-getChild(1).directEncode(satModel, i), getChild(0).directEncode(satModel, i), -aux);
                }
                else {
                    satModel.addClause(-getChild(1).directEncode(satModel, i), getChild(0).directEncode(satModel, i));
                }
            }
        }
    }

    public void toSMT(SMT satModel) throws IOException {
        if (usesSMTEncoding())
            satModel.addSMTClause(smtEncodeBool(satModel));
        else
            toSAT(satModel);
    }

    public boolean usesSMTEncoding() { return CmdFlags.getUseBV() || CmdFlags.getUseNIA() ||CmdFlags.getUseLIA() || (CmdFlags.getUseIDL() && canIDLEncode()); }

    public boolean canIDLEncode() {
        if (getChild(0).canVariableEncode() && getChild(1).canVariableEncode())
            // If we are comparing two identifiers, we can IDL encode
            return true;
        if (getChild(0) instanceof ShiftMapper && getChild(1) instanceof Identifier)
            return true;
        if (getChild(0) instanceof Identifier && getChild(1) instanceof ShiftMapper)
            return true;

        // Otherwise, we can only IDL encode if one of the parts is a number constant and
        // the other can be encoded into IDL
        boolean ch0_is_const = getChild(0) instanceof NumberConstant && getChild(1).canIDLEncode();
        boolean ch1_is_const = getChild(0).canIDLEncode() && getChild(1) instanceof NumberConstant;

        return ch0_is_const || ch1_is_const;
    }


    public String smtEncodeBool(SMT satModel) {

        String s = "(= ";

        if (CmdFlags.getUseBV()){
            s += getChild(0).smtEncodeBV(satModel) + " " + getChild(1).smtEncodeBV(satModel) + ")";
        }
        else {
            s += getChild(0).smtEncodeInt(satModel) + " " + getChild(1).smtEncodeInt(satModel) + ")";
        }
        return s;
    }

    public String smtEncodeInt(SMT satModel) {
        return "(ite " + smtEncodeBool(satModel) + " 1 0)";
    }

    public String smtEncodeBV(SMT satModel) {

        return "(ite " + smtEncodeBool(satModel) + " " + BitVector.toHexString(1) + " " + BitVector.toHexString(0) + ")";
    }
    
    public void toMIP(BufferedWriter b) throws IOException {
        if(getChild(0) instanceof WeightedSum || getChild(0) instanceof UnaryMinus || getChild(0) instanceof Identifier) {
            assert getChild(1).isConstant();
            getChild(0).toMIP(b);
            b.append(" = ");
            b.append(getChild(1).toString());
        }
        else if(getChild(1) instanceof WeightedSum || getChild(1) instanceof UnaryMinus || getChild(1) instanceof Identifier) {
            assert getChild(0).isConstant();
            getChild(1).toMIP(b);
            b.append(" = ");
            b.append(getChild(0).toString());
        }
        else {
            System.out.println(this);
            assert false : "missing case in toMip";
        }
    }
    
    public boolean childrenAreSymmetric() {
        return true;
    }
    
    public boolean canChildBeConvertedToDifference(int childIndex) {
        return isMyOnlyOtherSiblingEqualZero(childIndex);
    }

}
