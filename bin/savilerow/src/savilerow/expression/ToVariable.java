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
import java.io.StringWriter;
import java.util.ArrayList;

import savilerow.*;
import savilerow.model.*;

/* =============================================================================

Class to contain an ASTNode and a variable Identifier (or a constant)

Represents reification to the variable if the ASTNode is a relation.
If the ASTNode is arithmetic, it represents equality with the variable.

For example, ToVariable(x+y+z, aux1)   represents the constraint 
x+y+z=aux1

and ToVariable(AllDifferent(blah), aux1) represents
reify(alldiff(blah), aux1)

May also contain !aux1 as reification variable. 

==============================================================================*/

public class ToVariable extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public ToVariable(ASTNode constraint, ASTNode var)
    {
        super(constraint, var);
    }
    
    public ASTNode copy()
    {
        return new ToVariable(getChild(0), getChild(1));
    }
    
    public boolean isRelation() {return true; }
    public boolean strongProp() {
        return getChild(0).strongProp() && getChild(1).strongProp();
    }
    
    public String toString() {
        return "("+getChild(0)+"=tv="+getChild(1)+")";
    }
    
    // Similar simplify method to Equals.
    public ASTNode simplify() {
        // Special case to protect Reify -- if the first child is a constant or a single variable, turn it into iff.
        if(getChild(0) instanceof BooleanConstant || (getChild(0) instanceof Identifier && getChild(0).isRelation())) {
            detachChildren();
            if(getChild(1).isRelation()) {
                return new Iff(getChild(0), getChild(1));
            }
            else {
                return new Equals(getChild(0), getChild(1));
            }
        }
        
        if(getChild(0) instanceof NumberConstant || (getChild(0) instanceof Identifier && getChild(0).isNumerical())) {
            detachChildren();
            return new Equals(getChild(0), getChild(1));
        }
        
        if(CmdFlags.getSattrans() && ((getChild(0) instanceof ShiftMapper) || (getChild(0) instanceof MultiplyMapper))) {
            // When translating to SAT -- in rare cases, shift(x, i)=tv=aux appears after simplifying a sum on the lhs. 
            detachChildren();
            return new Equals(getChild(0), getChild(1));
        }
        
        if(getChild(0).equals(getChild(1))) {  // If symbolically equal, return true.
            return new BooleanConstant(true);
        }
        if(getChild(0).isConstant() && getChild(1).isConstant()) {
            // If equal when interpreted as integer.... (includes 1=true)
            return new BooleanConstant( getChild(0).getValue() == getChild(1).getValue() );
        }
        
        //  Check assignment of RHS in Boolean case. 
        if(getChild(1).isConstant() && getChild(1).getValue()==1 && getChild(0).isRelation()) {
            getChild(0).setParent(null);
            return getChild(0);
        }
        
        //  Check bounds
        Intpair b0=getChild(0).getBounds();
        Intpair b1=getChild(1).getBounds();
        
        if(b0.lower>b1.upper) {
            return new BooleanConstant(false);  // lower bound of c1 is greater than upper bound of c2.
        }
        if(b0.upper<b1.lower) {
            return new BooleanConstant(false);  // upper bound of c1 is less than lower bound of c2.
        }
        
        //  Optimisation for element constraint on a constant matrix, when targeting Minion.
        //  Turn it into a binary table.
        if(CmdFlags.getMiniontrans() && false) {
            ASTNode c0=getChild(0);
            if(c0 instanceof ElementOne || c0 instanceof SafeElementOne) {
                if(c0.getChild(0).getCategory() == ASTNode.Constant && (getChild(1) instanceof Identifier)) {
                    
                    //  Get the constant matrix.
                    /*ASTNode mat=getChild(0).getChildConst(0);
                    
                    //  Indexing is 0 or 1 based. 
                    int base=(c0 instanceof Element || c0 instanceof SafeElement)?0:1;
                    
                    ArrayList<ASTNode> table=new ArrayList<ASTNode>(mat.numChildren()-1);
                    
                    for(int i=1; i<mat.numChildren(); i++) {
                        //  finish here.
                    }*/
                    
                    TabulationUtils tu=new TabulationUtils(getChild(1).getModel());
                    
                    //  Look up in the cache for a long table. 
                    TabulationUtils.RetPair ret=tu.tryCacheNormalised(this, false);
                    
                    if(ret.nodereplace!=null) {
                        return ret.nodereplace.current_node;
                    }
                    
                    //  Normalise before making a table.
                    ASTNode a=tu.normalise(this);
                    
                    ASTNode newTable = tu.makeTableLong(a);
                    
                    tu.saveToCacheNormalised(ret.expstring, a, newTable);
                    
                    return newTable;
                }
            }
        }
        return null;
    }
    
    //  If contained in a Negate, push the negation inside 
    @Override
    public boolean isNegatable() {
        return getChild(1).isRelation();
    }
    @Override
    public ASTNode negation() {
        return new ToVariable(getChild(0), new Negate(getChild(1)));
    }
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
    {
        assert bool_context;
        if(getChild(0).isRelation() && !(getChild(0) instanceof SafeElementOne) && !(getChild(0) instanceof ElementOne))
        {
            b.append("reify(");
            getChild(0).toMinion(b, true);
            b.append(", ");
            getChild(1).toMinion(b, false);
            b.append(")");
        }
        else
        {
            getChild(0).toMinionWithAuxVar(b, getChild(1));
        }
    }
    
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        if(getChild(0).isRelation() && !(getChild(0) instanceof ElementOne)) {
            //assert ! (getChild(0) instanceof ToVariable);  not true -- can contain tovar(weightedsum)
            // Some constraints have a non-standard name without the _reif at the end
            if(getChild(0) instanceof And || getChild(0) instanceof Or) {
                getChild(0).toFlatzincWithAuxVar(b, getChild(1));
            }
            else {
                // Assume standard naming. i.e. c_reif is the reified version of c.
                // Get the unreified constraint into temp
                //StringBuilder temp=new StringBuilder();
                StringWriter sw=new StringWriter();
                BufferedWriter tempbw=new BufferedWriter(sw);
                
                getChild(0).toFlatzinc(tempbw, true);
                
                tempbw.flush();
                StringBuffer temp=new StringBuffer();
                temp.append(sw.toString());
                
                StringWriter swaux=new StringWriter();
                BufferedWriter tempbwaux=new BufferedWriter(swaux);
                
                getChild(1).toFlatzinc(tempbwaux, true);
                
                tempbwaux.flush();
                // replace ); with  ,tempaux);
                // or )::  with ,tempaux)::
                int t1=temp.lastIndexOf(");");
                if(t1!=-1) {
                    temp.replace(t1, t1+2, ","+swaux.toString()+");");
                }
                else {
                    t1=temp.lastIndexOf(")::");
                    temp.replace(t1, t1+3, ","+swaux.toString()+")::");
                }
                
                // replace ( with _reif(
                int t2=temp.indexOf("(");
                temp.replace(t2, t2+1, "_reif(");
                
                b.append(temp);
            }
        }
        else {
            // Numerical
            getChild(0).toFlatzincWithAuxVar(b, getChild(1));
        }
    }
    
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("( ");
        if(getChild(0).isRelation()) {
            getChild(0).toMinizinc(b, true);
            b.append(" <-> ");
            getChild(1).toMinizinc(b, true);
        }
        else {
            getChild(0).toMinizinc(b, false);
            b.append(" == ");
            getChild(1).toMinizinc(b, false);
        }
        if(getChild(1) instanceof Identifier && ((Identifier)getChild(1)).isAuxiliary()) {
            b.append(":: defines_var(");
            getChild(1).toMinizinc(b, getChild(0).isRelation());
            b.append(")");
        }
        b.append(" )");
    }
    
    //  Similar to Equals and Iff.
    public Long toSATLiteral(Sat satModel) {
        if(getChild(0).isConstant()) {
            return getChild(1).directEncode(satModel, getChild(0).getValue());
        }
        if(getChild(1).isConstant()) {
            if(getChild(0) instanceof SATLiteral || getChild(0) instanceof Identifier) {
                return getChild(0).directEncode(satModel, getChild(1).getValue());
            }
        }
        return null;
    }
    
    public void toSAT(Sat satModel) throws IOException
    {
        if(getChild(0).isRelation())
        {
            if (getChild(1) instanceof BooleanConstant) {
                if(getChild(1).getValue()==1){
                    getChild(0).toSAT(satModel);
                }
                else {
                    assert getChild(1).getValue()==0;
                    new Negate(getChild(0)).toSAT(satModel);
                }
            }
            else {
                getChild(0).toSATWithAuxVar(satModel, getChild(1).directEncode(satModel, 1));
                //  Can have child 0 be boolean and rhs be integer because 
                //  sums containing boolean terms can simplify to a single boolean term.
                //  Restrict rhs to 0..1 in this case.
                if(!getChild(1).isRelation()) {
                    ArrayList<Intpair> intervals=getChild(1).getIntervalSetExp();
                    for(int i=0; i<intervals.size(); i++) {
                        for(long j=intervals.get(i).lower; j<=intervals.get(i).upper; j++) {
                            if(j<0 || j>1) {
                                satModel.addClause(-getChild(1).directEncode(satModel, j));
                            }
                        }
                    }
                }
            }
        }
        else
        {
            // Call the toSATWithAuxVar method that takes an ASTNode.
            getChild(0).toSATWithAuxVar(satModel, getChild(1));
        }
    }
    
    @Override
    public boolean usesSMTEncoding() {
        if (CmdFlags.getUseNIA() || CmdFlags.getUseLIA() || CmdFlags.getUseBV()) {
            return getChild(0).usesSMTEncoding() && getChild(1).usesSMTEncoding();
        }
        else if (CmdFlags.getUseIDL()) {
            if (getChild(0).isRelation()) {
                return getChild(0).usesSMTEncoding() && getChild(1).canVariableEncode();
            }
            else {
                return getChild(0).canVariableEncode() && getChild(1).canVariableEncode();
            }
        }
        
        return false;
    }
    
    public boolean booleanBounds(Intpair x) {
        return x.lower >= 0 && x.upper <= 1;
    }
    
    public void toSMT(SMT satModel) throws IOException
    {
        if(getChild(0).isRelation() && !(getChild(0) instanceof SafeElementOne) && !(getChild(0) instanceof ElementOne) )
        {
            if (getChild(1) instanceof BooleanConstant) {
    		    if(getChild(1).getValue()==1){
                    getChild(0).toSMT(satModel);
                }
                else {
                    assert getChild(1).getValue()==0;
                    new Negate(getChild(0)).toSMT(satModel);
                }
            }
            else {
                if (!getChild(1).isRelation()) {

                    if (booleanBounds(getChild(1).getBounds())){

                        if (usesSMTEncoding()) {

                            satModel.addSMTClause("(= " + getChild(0).smtEncodeBool(satModel) + " " + getChild(1).smtEncodeBool(satModel) + ")");
                        }
                        else {
                            getChild(0).toSATWithAuxVar(satModel, getChild(1).directEncode(satModel, 1));
                        }
                    }
                    else { CmdFlags.errorExit("ToVariable Isn't Boolean"); }
                }
                else {
                    assert getChild(1).isRelation();

                    if (usesSMTEncoding())
                        satModel.addSMTClause("(= " + getChild(0).smtEncodeBool(satModel) + " " + getChild(1).smtEncodeBool(satModel) + ")");
                    else {
                        getChild(0).toSATWithAuxVar(satModel, getChild(1).directEncode(satModel, 1));
                    }
                }
            }
        }
        else {
            if (usesSMTEncoding()) {
                if (CmdFlags.getUseBV()) {
                    satModel.addSMTClause("(= " + getChild(0).smtEncodeBV(satModel) + " " + getChild(1).smtEncodeBV(satModel) + ")");
                }
                else {
                    satModel.addSMTClause("(= " + getChild(0).smtEncodeInt(satModel) + " " + getChild(1).smtEncodeInt(satModel) + ")");
                }
            }
            else {
                // Call the toSATWithAuxVar method that takes an ASTNode.
                getChild(0).toSATWithAuxVar(satModel, getChild(1));
            }
        }
    }
    
    @Override
    public String smtEncodeBool(SMT satModel) {
        try {

            if(getChild(0).isRelation() && !(getChild(0) instanceof SafeElementOne) && !(getChild(0) instanceof ElementOne) )
            {
                if (getChild(1) instanceof BooleanConstant) {
                    if(getChild(1).getValue()==1){
                        getChild(0).toSMT(satModel);
                    }
                    else {
                        assert getChild(1).getValue()==0;
                        new Negate(getChild(0)).toSMT(satModel);
                    }
                }
                else {
                    if (!getChild(1).isRelation()) {

                        if (booleanBounds(getChild(1).getBounds())){

                            if (usesSMTEncoding()) {

                                satModel.addSMTClause("(= " + getChild(0).smtEncodeBool(satModel) + " " + getChild(1).smtEncodeBool(satModel) + ")");
                            }
                            else {
                                getChild(0).toSATWithAuxVar(satModel, getChild(1).directEncode(satModel, 1));
                            }
                        }
                        else { CmdFlags.errorExit("ToVariable Isn't Boolean"); }
                    }
                    else {
                        assert getChild(1).isRelation();

                        if (usesSMTEncoding())
                            satModel.addSMTClause("(= " + getChild(0).smtEncodeBool(satModel) + " " + getChild(1).smtEncodeBool(satModel) + ")");
                        else
                            getChild(0).toSATWithAuxVar(satModel, getChild(1).directEncode(satModel, 1));
                    }
                }
            }
            else
            {
                if (usesSMTEncoding()) {
                    if (CmdFlags.getUseBV()) {
                        return "(= " + getChild(0).smtEncodeBV(satModel) + " " + getChild(1).smtEncodeBV(satModel) + ")";
                    }
                    else {
                        return "(= " + getChild(0).smtEncodeInt(satModel) + " " + getChild(1).smtEncodeInt(satModel) + ")";
                    }
                }
                else {
                        // Call the toSATWithAuxVar method that takes an ASTNode.
                        getChild(0).toSATWithAuxVar(satModel, getChild(1));
                }
            }
        }
        catch (IOException e) {
            CmdFlags.errorExit("Failed to encode ToVariable as Bool");
        }

        return "";
    }

    @Override
    public void toSATWithAuxVar(Sat satModel, long auxIn) throws IOException
    {
        if(getChild(0).isRelation())
        {
            long auxCt=satModel.createAuxSATVariable();
            getChild(0).toSATWithAuxVar(satModel, auxCt);
            
            // auxCt <-> satLit iff auxIn.
            
            // Child 1 must be a SATLiteral. A negation would already have been applied.
            long satLit;
            if(getChild(1) instanceof SATLiteral) {
                satLit=((SATLiteral) getChild(1)).getLit();
            }
            else {
                if(! getChild(1).isRelation()) {
                    System.err.println("Weird expression in output: "+this);
                }
                satLit=((Identifier) getChild(1)).directEncode(satModel, 1);
            }
            
            // auxIn implies auxCt=satLit
            satModel.addClause(-auxIn, -auxCt, satLit);
            satModel.addClause(-auxIn, auxCt, -satLit);
            
            //  not(AuxIn) implies auxCt!=satLit
            satModel.addClause(auxIn, -auxCt, -satLit);
            satModel.addClause(auxIn, auxCt, satLit);
        }
        else
        {
            CmdFlags.errorExit("Missing part of toSATWithAuxVar(long) method on type ToVariable.");
        }
    }
}

