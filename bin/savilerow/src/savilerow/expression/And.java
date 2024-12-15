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
import java.util.HashSet;
import java.util.LinkedHashSet;

import savilerow.*;
import savilerow.model.*;

public class And extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public And(ArrayList<ASTNode> ch) {
        super(ch);
    }
    
    public And(ASTNode[] ch) {
        super(ch);
    }
    
    // Ctor to help replace binop.
    public And(ASTNode l, ASTNode r) {
        super(l, r);
    }
    
    public ASTNode copy() {
        return new And(getChildrenArray());
    }
    public boolean isRelation() { return true; }
    public boolean strongProp() {
        for(int i=0; i<numChildren(); i++) {
            if(!getChild(i).strongProp()) {
                return false;
            }
        }
        
        //  Check for overlapping scopes. 
        HashSet<ASTNode> variableSet=new HashSet<>();
        variableSet.addAll(TabulationUtils.getVariablesOrdered(getChild(0)));
        for(int i=1; i<numChildren(); i++) {
            ArrayList<ASTNode> vars=TabulationUtils.getVariablesOrdered(getChild(i));
            for(int j=0; j<vars.size(); j++) {
                if(variableSet.contains(vars.get(j))) {
                    // Overlapping scopes, will not get GAC
                    return false;
                }
            }
            variableSet.addAll(vars);
        }
        
        return true;
    }
    
    public ASTNode simplify() {
        boolean changed = false;

        ArrayList<ASTNode> ch = getChildren();
        for (int i =0; i < ch.size(); i++) {
            if (ch.get(i) instanceof And) {
                changed = true;
                ASTNode curnode = ch.remove(i);
                i--;                // current element removed so move back in list.
                // Add children to end of this list, so that the loop will process them.
                ch.addAll(curnode.getChildren());
            }
        }

        // Constant folding
        for (int i =0; i < ch.size(); i++) {
            if (ch.get(i).isConstant()) {
                long val = ch.get(i).getValue();
                if (val == 1) {
                    changed = true;
                    ch.remove(i);
                    i--;
                } else {                    // Found a False in the conjunction.
                    if(CmdFlags.dominanceRelation) {
                        // hack
                        for(int j=ch.size()-1; j>=0; j--) {
                            if(j!=i && !(ch.get(j) instanceof IncomparabilityFunction)) {
                                ch.remove(j);
                                changed=true;
                            }
                        }
                        break;
                    }
                    return new BooleanConstant(false);
                }
            }
        }
        
        // remove duplicates
        LinkedHashSet<ASTNode> a = new LinkedHashSet<ASTNode>(ch);
        if (a.size() < ch.size()) {
            changed = true;
            ch.clear();
            ch.addAll(a);
        }
        
        if (ch.size() == 0) {
            return new BooleanConstant(true);
        }
        if (ch.size() == 1) {
            ch.get(0).setParent(null);
            return ch.get(0);
        }
        if (changed) {
            // Recycle the children instead of copying.
            for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
            return new And(ch);
        }
        return null;
    }

    // If contained in a Negate, push the negation inside using De Morgens law.
    @Override
    public boolean isNegatable() {
        return true;
    }
    @Override
    public ASTNode negation() {
        ArrayList<ASTNode> newchildren = new ArrayList<ASTNode>();

        for (int i =0; i < numChildren(); i++) {
            newchildren.add(new Negate(getChild(i)));
        }

        return new Or(newchildren);
    }
    
    @Override
	public int polarity(int child) {
	    return polarity();
	}
	
    public boolean typecheck(SymbolTable st) {
        for (ASTNode child : getChildren()) {
            if (!child.typecheck(st)) {
                return false;
            }
            if (!child.isRelation()) {
                System.out.println("ERROR: 'And' contains something other than a relation:" + child);
                return false;
            }
        }
        return true;
    }

    public ASTNode normalise() {
        if (getParent() instanceof Top) {
            // Don't normalise the top level and -- no point.
            return this;
        }
        normaliseInPlace();
        
        return this;
    }
    
    public ASTNode normaliseAlpha() {
        if (getParent() instanceof Top) {
            // Don't normalise the top level and -- no point.
            return null;
        }
        normaliseInPlaceAlpha();
        
        return null;
    }

    public boolean isCommAssoc() {
        return true;
    }

    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {        // Special case for the top of the tree.
        assert bool_context;        // parent had better expect a constraint.
        if (getParent() instanceof Top) {
            for (int i =0; i < numChildren(); i++) {
                getChild(i).toMinion(b, true);
                b.append("\n");
            }
        } else {
            b.append("watched-and({");
            for (int i =0; i < numChildren(); i++) {
                getChild(i).toMinion(b, true);
                if (i < numChildren() - 1) {
                    b.append(",");
                }
            }
            b.append("})");
        }
    }

    public String toString() {
        StringBuilder b = new StringBuilder();
        if (getParent() instanceof Top) {
            for (int i =0; i < numChildren(); i++) {
                b.append(getChild(i).toString());
                if (i < numChildren() - 1) {
                    b.append(",\n");
                }
            }
        } else {
            b.append("(");
            for (int i =0; i < numChildren(); i++) {
                b.append(getChild(i).toString());
                if (i < numChildren() - 1) {
                    b.append(" /\\ ");
                }
            }
            b.append(")");
        }
        return b.toString();
    }
    
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        // assert inTopConjunction();
        for (int i =0; i < numChildren(); i++) {
            if (getChild(i) instanceof Identifier) {
                // It's a bare identifier, should be of a boolean variable
                b.append("constraint bool_eq(");
                getChild(i).toFlatzinc(b, true);
                b.append(",true);\n");
            } else {
                getChild(i).toFlatzinc(b, false);
                b.append("\n");
            }
        }
    }

    @Override
    public boolean inTopConjunction() {
        return getParent().inTopConjunction();
    }
    @Override
    public boolean inTopAnd() {
        return getParent().inTopAnd();
    }
    @Override
    public void toFlatzincWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException {
        b.append("constraint array_bool_and([");
        for (int i =0; i < numChildren(); i++) {
            getChild(i).toFlatzinc(b, true);
            if (i < numChildren() - 1) {
                b.append(",");
            }
        }
        b.append("],");
        aux.toFlatzinc(b, true);
        b.append(");");
    }
    @Override
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        assert bool_context;
        if (inTopConjunction()) {
            for (int i =0; i < numChildren(); i++) {
                if (getChild(i) instanceof Identifier) {
                    // It's a bare identifier, should be of a boolean variable
                    b.append("constraint ");
                    getChild(i).toMinizinc(b, true);
                    b.append(" <-> true;\n");
                } else {
                    b.append("constraint ");
                    getChild(i).toMinizinc(b, true);
                    b.append(";\n");
                }
            }
        } else {
            b.append("(");
            for (int i =0; i < numChildren(); i++) {
                getChild(i).toMinizinc(b, true);
                if (i < numChildren() - 1) {
                    b.append(" /\\ ");
                }
            }
            b.append(")");
        }
    }
    
    public void toSAT(Sat satModel) throws IOException {
        for(int i=0; i<numChildren(); i++) {
            ASTNode child=getChild(i);
            satModel.addComment(String.valueOf(child).replaceAll("\n", " "));
            if (child instanceof Negate) {
                satModel.addClause(child.getChild(0).directEncode(satModel,0));
            } else if (child instanceof Identifier) {
                satModel.addClause(child.directEncode(satModel, 1));
            } else {
                // Any constraint
                child.toSAT(satModel);
            }
        }
    }

    public void toSMT(SMT satModel) throws IOException {
        for(int i=0; i<numChildren(); i++) {
            ASTNode child=getChild(i);
            satModel.addComment(String.valueOf(child).replaceAll("\n", " "));
            if (child instanceof Negate) {
                satModel.addClause(child.getChild(0).directEncode(satModel,0));
            } else if (child instanceof Identifier) {
                satModel.addClause(child.directEncode(satModel, 1));
            } else {
                // Any constraint
                child.toSMT(satModel);
            }
        }
    }

    @Override
    public String smtEncodeBool(SMT satModel) {
        String s = "(and";

        for (ASTNode child : getChildren())
            s += " " + child.smtEncodeBool(satModel);

        return s + ")";
    }

    @Override
    public String smtEncodeBV(SMT satModel) {
        return "(ite " + this.smtEncodeBool(satModel) + " " + SMT.toSMTBV(1) + " " + SMT.toSMTBV(0) + ")";
    }

    @Override
    public String smtEncodeInt(SMT satModel) { return "(ite " + this.smtEncodeBool(satModel) + " 1 0)"; }

    public boolean usesSMTEncoding() {
        return true;
    }

    public void toSATWithAuxVar(Sat satModel, long auxVar) throws IOException {
        // Encode as:
        // -child0 \/ -child1 \/ ...  <-> -auxVar
        ArrayList<Long> c=new ArrayList<Long>(numChildren());
        
        for(int i=0; i<numChildren(); i++) {
            c.add(getChild(i).directEncode(satModel,0));   //  SATLiteral and bool var have directEncode. Other types are not expected here.
        }
        
        satModel.addClauseReified(c, -auxVar);
    }
    
    public void toMIP(BufferedWriter b) throws IOException {
        if(getParent() instanceof Top) {
            //  Top-level constraints. 
            for(int i=0; i<numChildren(); i++) {
                b.append("c");
                b.append(String.valueOf(i+1));
                b.append(": ");
                System.out.println(getChild(i));
                getChild(i).toMIP(b);
                b.append("\n");
            }
        }
        else {
            System.out.println(this);
            System.out.println(getParent());
            assert false : "Missing case in toMIP";
        }
    }
    
    @Override
    public boolean childrenAreSymmetric() {
        return true;
    }
}
