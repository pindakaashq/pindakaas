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
import savilerow.model.*;

//  Logical implication.
//  When targeting Minion, also appears in output as reifyimply. 

public class Implies extends LogicBinOp
{
    public static final long serialVersionUID = 1L;
    public Implies(ASTNode l, ASTNode r)
    {
        super(l, r);
    }
    
    public ASTNode copy()
    {
        return new Implies(getChild(0), getChild(1));
    }
    public boolean isRelation(){return true;}
    public boolean strongProp() {
        return getChild(0).strongProp() && getChild(1).strongProp();
    }
    
    public ASTNode simplify() {
        //  Basic rewrites -- one child is a constant
        if(getChild(0).isConstant() && getChild(0).getValue()==1) {
            getChild(1).setParent(null);
            return getChild(1);
        }
        if(getChild(0).isConstant() && getChild(0).getValue()==0) {
            return new BooleanConstant(true);
        }
        if(getChild(1).isConstant() && getChild(1).getValue()==1) {
            return new BooleanConstant(true);
        }
        if(getChild(1).isConstant() && getChild(1).getValue()==0) {
            getChild(0).setParent(null);
            return new Negate(getChild(0));
        }
        
        // Two children are symbolically equal
        if(getChild(0).equals(getChild(1))) return new BooleanConstant(true);
        
        if(getChild(0) instanceof And || getChild(1) instanceof Or) {   // Could also have getChild(1) is Implies, getParent is Or.
            //  In both of these cases the implication can merge into an existing disjunction.
            detachChildren();
            return new Or(new Negate(getChild(0)), getChild(1));
        }
        
        // Right side is a conjunction -- lift it through the implication.
        if(getChild(1) instanceof And) {
            ASTNode[] tmp=new ASTNode[getChild(1).numChildren()];
            for(int i=0; i<getChild(1).numChildren(); i++) {
                getChild(1).getChild(i).setParent(null);
                tmp[i]=new Implies(getChild(0), getChild(1).getChild(i));
            }
            return new And(tmp);
        }
        
        //   c <= var -> d <= var  and d<=c  ----> true.
        if((getChild(0) instanceof Less || getChild(0) instanceof LessEqual) &&
            (getChild(1) instanceof Less || getChild(1) instanceof LessEqual) &&
            (getChild(0).getChild(1).equals(getChild(1).getChild(1))) ) {
            ASTNode c=getChild(0).getChild(0);
            ASTNode d=getChild(1).getChild(0);
            if(c.isConstant() && d.isConstant()) {
                long c1=c.getValue();
                long d1=d.getValue();
                if(getChild(0) instanceof Less) {
                    c1++;   //  treat as LessEqual by adjusting the constant.
                }
                if(getChild(1) instanceof Less) {
                    d1++;
                }
                
                if(d1<=c1) {
                    return new BooleanConstant(true);
                }
            }
        }
        
        //  Both children negated -- strip off negations.
        //  -A -> -B   ~~~>  B -> A
        if(getChild(0) instanceof Negate && getChild(1) instanceof Negate) {
            return new Implies(getChild(1).getChild(0), getChild(0).getChild(0));
        }
        
        return null;
    }
    
    //  If contained in a Negate, push the negation inside using De Morgens law. 
    @Override
    public boolean isNegatable() {
        return true;
    }
    @Override
    public ASTNode negation() {
        return new And(getChild(0), new Negate(getChild(1)));
    }
    @Override
    public int polarity(int child) {
        if(child==0) {
            return -polarity();
        }
        else {
            assert child==1;
            return polarity();
        }
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        for(ASTNode child :  getChildren()) {
            if(!child.typecheck(st)) {
                return false;
            }
            if(!child.isRelation()) {
                System.out.println("ERROR: Implication contains non-Boolean expression:"+child);
                return false;
            }
        }
        for(int i=0; i<2; i++) {
	        if(getChild(i) instanceof Iff || getChild(i) instanceof Implies) {
	            CmdFlags.println("ERROR: Nested non-associative operators: "+this);
	            CmdFlags.println("ERROR: Add brackets to remove ambiguity.");
	            return false;
	        }
        }
        return true;
    }
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
    {
        assert bool_context;
        if(getChild(1) instanceof Identifier || ( getChild(1) instanceof Negate && getChild(1).getChild(0) instanceof Identifier )) { 
            b.append("ineq(");
            getChild(0).toMinion(b, false);
            b.append(", ");
            getChild(1).toMinion(b, false);
            b.append(", 0)");
        }
        else {
            // reify imply
            b.append("reifyimply(");
            getChild(1).toMinion(b, true);
            b.append(", ");
            getChild(0).toMinion(b, false);
            b.append(")");
        }
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        if(CmdFlags.getOrtoolstrans()) {
            //  No bool_clause constraint. Does not allow negation, see toFlatten method of Negate. 
            
            b.append("constraint bool_le(");
            getChild(0).toFlatzinc(b, true);
            b.append(",");
            getChild(1).toFlatzinc(b, true);
            b.append(");");
        }
        else {
            b.append("constraint bool_clause([");
            boolean second=false;
            // Positive literals
            if(getChild(0) instanceof Negate) {
                getChild(0).getChild(0).toFlatzinc(b, true);  // Strip off the negation.
                second=true;
            }
            if(! (getChild(1) instanceof Negate)) {
                if(second) b.append(",");
                getChild(1).toFlatzinc(b, true);
            }
            b.append("],[");
            // Negative literals
            second=false;
            if(! (getChild(0) instanceof Negate)) {
                getChild(0).toFlatzinc(b, true);
                second=true;
            }
            if(getChild(1) instanceof Negate) {
                if(second) b.append(",");
                getChild(1).getChild(0).toFlatzinc(b, true);  // Strip off the negation.
            }
            b.append("]);");
        }
    }
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("(");
        getChild(0).toMinizinc(b, true);
        b.append("->");
        getChild(1).toMinizinc(b, true);
        b.append(")");
    }
    @Override
    public void toSAT(Sat satModel) throws IOException {
        assert getChild(0).hasLiteralEncoding();
        if(getChild(1).hasLiteralEncoding()) {
            satModel.addClause(getChild(0).directEncode(satModel,0), getChild(1).directEncode(satModel,1) );
        }
        else {
            satModel.addContextLit(getChild(0).directEncode(satModel, 0));
            getChild(1).toSAT(satModel);
            satModel.deleteContextLit();
        }
    }
    @Override
    public void toSATWithAuxVar(Sat satModel, long aux) throws IOException {
        ArrayList<Long> c=new ArrayList<Long>();
        c.add(getChild(0).directEncode(satModel,0));
        c.add(getChild(1).directEncode(satModel,1));
        satModel.addClauseReified(c, aux);
    }
    
    @Override
    public boolean usesSMTEncoding() { return CmdFlags.getUseBV() || CmdFlags.getUseNIA() || CmdFlags.getUseLIA() || CmdFlags.getUseIDL(); }

    public void toSMT(SMT satModel) throws IOException {
        satModel.addSMTClause(smtEncodeBool(satModel));
    }

    public String smtEncodeBool(SMT satModel) {
        return "(or (not " + getChild(0).smtEncodeBool(satModel) + ") " + getChild(1).smtEncodeBool(satModel) + ")";
    }

    @Override
    public String smtEncodeBV(SMT satModel) {

        return "(ite " + this.smtEncodeBool(satModel) + " " + SMT.toSMTBV(1) + " " + SMT.toSMTBV(0) + ")";
    }

    @Override
    public String smtEncodeInt(SMT satModel) {
        return "(ite " + smtEncodeBool(satModel) + " 1 0)";
    }
    
    public String toString() {
        return "("+getChild(0)+" -> "+getChild(1)+")";
    }
    
}
