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

public class InSet extends BinOp
{
    public static final long serialVersionUID = 1L;
    public InSet(ASTNode a, ASTNode set)
    {
        super(a, set);
    }
    
    public ASTNode copy()
    {
        return new InSet(getChild(0), getChild(1));
    }
    public boolean isRelation(){return true;}
    public boolean strongProp() {
        return getChild(0).strongProp();  //  Delegates to integer expression on left.
    }
    
    public ASTNode simplify() {
        // If left side is a constant, evaluate.
        if(getChild(0).isConstant() && getChild(1).getCategory()==ASTNode.Constant) {
            if(getChild(1).containsValue(getChild(0).getValue())) {
                return new BooleanConstant(true);
            }
            else {
                return new BooleanConstant(false);
            }
        }
        
        if(getChild(1).getCategory()==ASTNode.Constant) {
            ArrayList<Intpair> intervals=getChild(1).getIntervalSet();
            if(intervals.size()==0) {
                // No values in set. 
                return new BooleanConstant(false);
            }
            
            if(intervals.size()==1) {
                // Compare to the bounds of the left side.
                Intpair s=intervals.get(0);
                Intpair p=getChild(0).getBounds();
                if(s.upper < p.lower || s.lower > p.upper) {
                    return new BooleanConstant(false);   // disjoint
                }
                if(p.lower>=s.lower && p.upper<=s.upper) {
                    return new BooleanConstant(true);
                }
            }
            
            if(intervals.size()==1 && intervals.get(0).lower==intervals.get(0).upper) {
                // Equality simpler than InSet, only one value so turn into equality.
                // Could also catch case where only one value is _not_ in the set, --> diseq.
                return new Equals(getChild(0), NumberConstant.make(intervals.get(0).lower));
            }
            
            //  If left side is a decision variable
            if(getChild(0) instanceof Identifier && getChild(0).getCategory()==ASTNode.Decision) {
                ASTNode dom=getChild(0).getModel().global_symbols.getDomain(getChild(0).toString());
                
                if(dom.getCategory() == ASTNode.Constant) {
                    ArrayList<Intpair> tmp=Intpair.setDifference(dom.getIntervalSet(), intervals);
                    
                    // subtract the set from the domain and see if there
                    // are any domain values left. If not, the inset is always true. 
                    if(tmp.size()==0) {
                        return new BooleanConstant(true);
                    }
                }
            }
        }
        
        return null;
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        if(!getChild(0).typecheck(st) || !getChild(1).typecheck(st)) {
            return false;
        }
        
        if(!getChild(1).isSet()) {
            CmdFlags.println("ERROR: Expected set on right hand side of 'in' operator: "+this);
            return false;
        }
        
        if(getChild(0).getDimension()>0 || getChild(0).isSet()) {
            CmdFlags.println("ERROR: Expected integer or boolean expression on left hand side of 'in' operator: "+this);
            return false;
        }
        
        return true;
    }
    
    public String toString() {
        return "("+getChild(0)+" in "+getChild(1)+")";
    }
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        assert bool_context;
        b.append("w-inintervalset(");
        getChild(0).toMinion(b, false);
        b.append(",[");
        ArrayList<Intpair> a=getChild(1).getIntervalSet();
        for(int i=0; i<a.size(); i++) {
            b.append(String.valueOf(a.get(i).lower));
            b.append(",");
            b.append(String.valueOf(a.get(i).upper));
            if(i<a.size()-1) b.append(",");
        }
        b.append("])");
    }
    
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("constraint set_in(");
        getChild(0).toFlatzinc(b, false);
        b.append(",{");
        b.append(Intpair.printValues(getChild(1).getIntervalSet()));
        b.append("});");
    }
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("(");
        getChild(0).toMinizinc(b, false);
        b.append(" in {");
        b.append(Intpair.printValues(getChild(1).getIntervalSet()));
        b.append("})");
    }
    public void toSAT(Sat satModel) throws IOException {
        satModel.unaryDirectEncoding(this, getChild(0));
    }
    public void toSATWithAuxVar(Sat satModel, long aux) throws IOException {
        satModel.unaryDirectEncodingWithAuxVar(this, getChild(0), aux);
    }
    public boolean test(long val) {
        return getChild(1).containsValue(val);
    }
    
    @Override
    public boolean usesSMTEncoding() {
        return CmdFlags.getUseBV() || CmdFlags.getUseNIA() || CmdFlags.getUseLIA() || CmdFlags.getUseIDL();
    }
    
    @Override
    public String smtEncodeBool(SMT satModel) {
        StringBuilder b = new StringBuilder();
        
        ArrayList<Intpair> values=getChild(1).getIntervalSet();
        
        if(values.get(0).lower != values.get(values.size()-1).upper) {
            b.append("(or");
        }
        
        String ch0;
        if (CmdFlags.getUseBV()) {
            ch0 = getChild(0).smtEncodeBV(satModel);
        }
        else {
            ch0 = getChild(0).smtEncodeInt(satModel);
        }
        
        
        for(int i=0; i<values.size(); i++) {
            for(long val=values.get(i).lower; val<=values.get(i).upper; val++) {
                b.append(" (= ");
                b.append(ch0);
                b.append(" ");

                if (CmdFlags.getUseBV()) { b.append(SMT.toSMTBV(val)); }
                else { b.append(SMT.toSMTInt(val)); }

                b.append(")");
            }
        }
        
        if(values.get(0).lower != values.get(values.size()-1).upper) {
            b.append(")");
        }
        return b.toString();
    }

    @Override
    public String smtEncodeBV(SMT satModel) {
        return "(ite " + this.smtEncodeBool(satModel) + " " + SMT.toSMTBV(1) + " " + SMT.toSMTBV(0) + ")";
    }

    @Override
    public String smtEncodeInt(SMT satModel) {
        return "(ite " + smtEncodeBool(satModel) + " 1 0)";
    }
}