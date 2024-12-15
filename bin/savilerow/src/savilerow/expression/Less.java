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

public class Less extends BinOp
{
    public static final long serialVersionUID = 1L;
	public Less(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public ASTNode copy()
	{
	    return new Less(getChild(0), getChild(1));
	}
	public boolean isRelation(){return true;}
	public boolean strongProp() {
        return true;   // Even if children are only obtaining bound consistency, < is still strong.
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
	    
	    if(getChild(0).equals(getChild(1))) return new BooleanConstant(false);
	    
	    Intpair a=getChild(0).getBounds();
	    Intpair b=getChild(1).getBounds();
	    
	    if(a.upper < b.lower) return new BooleanConstant(true);
	    if(a.lower >= b.upper) return new BooleanConstant(false);
	    
	    if(getChild(0).isConstant() && getChild(1).isConstant()) {
	        if(getChild(0).getValue()<getChild(1).getValue()) return new BooleanConstant(true);
	        else return new BooleanConstant(false);
	    }
	    
	    // Now simplify sum1<sum2 to sum1-sum2<=-1
	    // Changes to <= because that is the standard way of expressing sums. 
	    if(getChild(0) instanceof WeightedSum && getChild(1) instanceof WeightedSum) {
	        detachChildren();  // do not copy
	        return new LessEqual(BinOp.makeBinOp("-", getChild(0), getChild(1)), NumberConstant.make(-1));
	    }
	    
	    // Finally it helps identical CSE if sums have no constants in them. 
	    // Shift the constant to the other side. 
	    if(getChild(0) instanceof WeightedSum && getChild(0).getCategory()==ASTNode.Decision && getChild(1).getCategory()<ASTNode.Decision) {
	        Pair<ASTNode, ASTNode> p1=((WeightedSum)getChild(0)).retrieveConstant();
	        if(p1!=null) {
	            getChild(1).setParent(null);
	            return new Less(p1.getSecond(), BinOp.makeBinOp("-", getChild(1), p1.getFirst()));
	        }
	        else {
	            detachChildren();
	            return new LessEqual(getChild(0), BinOp.makeBinOp("-", getChild(1), NumberConstant.make(1)));
	        }
	    }
	    if(getChild(1) instanceof WeightedSum && getChild(1).getCategory()==ASTNode.Decision && getChild(0).getCategory()<ASTNode.Decision) {
	        Pair<ASTNode, ASTNode> p1=((WeightedSum)getChild(1)).retrieveConstant();
	        if(p1!=null) {
	            getChild(0).setParent(null);
	            return new Less(BinOp.makeBinOp("-", getChild(0), p1.getFirst()), p1.getSecond());
	        }
	        else {
	            detachChildren();
	            return new LessEqual(BinOp.makeBinOp("+", getChild(0), NumberConstant.make(1)), getChild(1));
	        }
	    }
	    
	    // Get rid of unary minus opposite a constant. 
	    if(getChild(0) instanceof UnaryMinus && getChild(1).isConstant()) {
	        return new Less(new UnaryMinus(getChild(1)), getChild(0).getChild(0));
	    }
	    if(getChild(1) instanceof UnaryMinus && getChild(0).isConstant()) {
	        return new Less(getChild(1).getChild(0), new UnaryMinus(getChild(0)));
	    }
	    
	    // Factor out the GCD of a sum.
	    if(getChild(0) instanceof WeightedSum && getChild(1).isConstant()) {
	        Pair<ASTNode, ASTNode> p=((WeightedSum)getChild(0)).factorOutGCD();
	        
	        if(p!=null) {
	            long gcd=p.getFirst().getValue();
	            long c=getChild(1).getValue();
	            
	            // Sum is on the left so need to round downwards when calculating c/gcd.
	            long rhs=Divide.div(c, gcd);
	            if(rhs*gcd != c) {
	                // Some rounding occurred so it softens from a less to less-equal. 
	                return new LessEqual(p.getSecond(), NumberConstant.make(rhs));
	            }
	            else {
	                return new Less(p.getSecond(), NumberConstant.make(rhs));
	            }
	        }
	    }
	    if(getChild(1) instanceof WeightedSum && getChild(0).isConstant()) {
	        Pair<ASTNode, ASTNode> p=((WeightedSum)getChild(1)).factorOutGCD();
	        
	        if(p!=null) {
	            long gcd=p.getFirst().getValue();
	            long c=getChild(0).getValue();
	            
	            // Sum is on the right so need to round upwards when calculating c/gcd.
	            //  4<= 3x+3y   becomes   1.33 <= x+y  becomes   2<=x+y
	            long lhs=Divide.divceil(c, gcd);
	            
                if(lhs*gcd != c) {
                    // Some rounding occurred so the less softens to a less-equal. 
                    return new LessEqual(NumberConstant.make(lhs), p.getSecond());
                }
                else {
                    return new Less(NumberConstant.make(lhs), p.getSecond());
                }
	        }
	    }
	    
	    /*
	    // Post-1.6 part, turn x<5 into x!=5 if 5 is the top of the domain. 
	    if(getChild(0) instanceof Identifier && getChild(1).isConstant() && a.e2.equals(getChild(1))) {
	        return new AllDifferent(getChild(0), getChild(1));
	    }
	    // 1<x where 1 is min(x) ---> x!=1
	    if(getChild(1) instanceof Identifier && getChild(0).isConstant() && b.e1.equals(getChild(0))) {
	        return new AllDifferent(getChild(0), getChild(1));
	    }
	    // Also two cases where it turns into equality. 
	    */
	    
	    return null;
	}
	
	@Override
	public boolean isNegatable() {
	    return true;
	}
	@Override
	public ASTNode negation() {
	    return new LessEqual(getChild(1), getChild(0));
	}
	
	@Override
	public int polarity(int child) {
	    return polarity()*((child==0)? -1 : 1);
	}
	
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    assert bool_context;
	    b.append("ineq(");
	    getChild(0).toMinion(b, false);
	    b.append(", ");
	    getChild(1).toMinion(b, false);
	    b.append(", -1)");
	}
	
	public String toString() {
	    return "("+getChild(0)+"<"+getChild(1)+")";
	}
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
	    b.append("constraint int_lt(");
	    getChild(0).toFlatzinc(b, false);
	    b.append(",");
	    getChild(1).toFlatzinc(b, false);
	    b.append(");");
	}
	public void toMinizinc(StringBuilder b, boolean bool_context) {
	    b.append("(");
	    getChild(0).toMinizinc(b, false);
	    b.append("<");
	    getChild(1).toMinizinc(b, false);
	    b.append(")");
	}
	
	////////////////////////////////////////////////////////////////////////////
	//  SAT encodings
	
	//  Support encoding seems better than order and direct encodings, in informal experiment with Black Hole
	
	public Long toSATLiteral(Sat satModel) {
	    if(getChild(0).isConstant()) {
	        if(getChild(1) instanceof SATLiteral) {
	            assert getChild(0).getValue()==0;   // The only sensible value. If it's anything else, simplify is incomplete.
	            return ((SATLiteral)getChild(1)).getLit();  // 0<b  rewrites to b
	        }
	        else {
	            return -getChild(1).orderEncode(satModel, getChild(0).getValue());  // a < x becomes !(x <= a)
	        }
        }
        if(getChild(1).isConstant()) {
            if(getChild(0) instanceof SATLiteral) {
	            assert getChild(1).getValue()==1;
	            return -((SATLiteral)getChild(0)).getLit();  // b<1  rewrites to -b
	        }
	        else {
	            return getChild(0).orderEncode(satModel, getChild(1).getValue()-1);  // x < a becomes x <= a-1
	        }
        }
        return null;
	}
	
	static boolean useOrderEnc=true;
	
    public void toSAT(Sat satModel) throws IOException {
        if(useOrderEnc) {
            toSATOrderEnc(satModel, 0);
        }
        else {
            satModel.supportEncodingBinary(this,getChild(0),getChild(1));
        }
    }

    public void toSMT(SMT satModel) throws IOException {
        if (usesSMTEncoding())
            satModel.addSMTClause(smtEncodeBool(satModel));
        else
            toSAT(satModel);
    }

    public boolean usesSMTEncoding() {
		return CmdFlags.getUseBV() || CmdFlags.getUseNIA() || CmdFlags.getUseLIA() || (CmdFlags.getUseIDL() && canIDLEncode());
    }

    public boolean canIDLEncode() {
        if (getChild(0) instanceof Identifier && getChild(1) instanceof Identifier)
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
        if (CmdFlags.getUseNIA() || CmdFlags.getUseLIA()) {
            String s = "(< ";

            s += getChild(0).smtEncodeInt(satModel) + " " + getChild(1).smtEncodeInt(satModel) + ")";

            return s;
        }
        else if (CmdFlags.getUseBV()) {

        	String s = "(bvslt ";

			s += getChild(0).smtEncodeBV(satModel) + " " + getChild(1).smtEncodeBV(satModel) + ")";

        	return s;
		}
        else if (CmdFlags.getUseIDL()) {
            // We have ch0 < ch1, so IDL encoding will be (< (- ch0 ch1) 0) meaning that ch0 - ch1 < 0
            String s = "(< ";

            s += getChild(0).smtEncodeInt(satModel) + " " + getChild(1).smtEncodeInt(satModel) + ")";

            return s;
        }

        return null;
    }

    @Override
    public String smtEncodeBV(SMT satModel) {

    	return "(ite " + this.smtEncodeBool(satModel) + " " + SMT.toSMTBV(1) + " " + SMT.toSMTBV(0) + ")";
	}

	@Override
	public String smtEncodeInt(SMT satModel) {
		return "(ite " + smtEncodeBool(satModel) + " 1 0)";
	}

    public void toSATWithAuxVar(Sat satModel, long aux) throws IOException {
        if(useOrderEnc) {
            toSATOrderEnc(satModel, -aux);
            // construct the negation
            (new LessEqual(getChild(1), getChild(0))).toSATOrderEnc(satModel, aux);
        }
        else {
            satModel.supportEncodingBinaryWithAuxVar(this,getChild(0),getChild(1),aux);
        }
    }
    
    //   For each value a,  [x <= a] \/ [y > a+1]
    //   i.e.  y<=a+1 -> x<=a      and   x>a -> y>a+1
    public void toSATOrderEnc(Sat satModel, long aux) throws IOException {
        ArrayList<Intpair> a=getChild(0).getIntervalSetExp();
        a=Intpair.union(a, Intpair.shiftIntervalSet(getChild(1).getIntervalSetExp(), -1));
        
        for(Intpair pair1 : a) {
            for (long i=pair1.lower; i<=pair1.upper; i++) {
                if(aux!=0) {
                    satModel.addClause(getChild(0).orderEncode(satModel, i), -getChild(1).orderEncode(satModel, i+1), aux);
                }
                else {
                    satModel.addClause(getChild(0).orderEncode(satModel, i), -getChild(1).orderEncode(satModel, i+1));
                }
            }
        }
    }
    
    public boolean test(long value1, long value2)
    {
        return value1<value2;
    }
}
