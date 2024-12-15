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

// ElementOne(matrix or matrix slice, index expression) is a function to the result.
//  One-based indexing

public class ElementOne extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public ElementOne(ASTNode arr, ASTNode ind) {
        super(arr, ind);
    }
    
	public ASTNode copy()
	{
	    return new ElementOne(getChild(0), getChild(1));
	}
	
	public boolean isRelation(){
	    return getChild(0).isRelation();}
	@Override public boolean strongProp() {
	    return getChild(0).strongProp() && getChild(1).strongProp();
	}
	public boolean isNumerical() {
        return getChild(0).isNumerical();}
    
    public boolean toFlatten(boolean propagate) {
        if(this.isNumerical()) {
            return true;
        }
        return super.toFlatten(propagate);  // Hand over to ASTNode.toFlatten
    }
    
	public ASTNode simplify() {
	    // if getChild(0) is an EmptyMatrix then index must be out of bounds -- so do nothing. 
        ASTNode mat=getChildConst(0);
        
        if(mat instanceof CompoundMatrix) {
            if(getChild(1).isConstant()) {     // If the index is a constant, evaluate it. 
                long idx=getChild(1).getValue();
                if(idx<1 || idx>=(mat.numChildren())) {
                    return null;   // out of bounds -- do not attempt to evaluate it. 
                }
                else {
                    ASTNode elem=mat.getChild( (int)idx );  // Index from 1. Index domain is in position 0.
                    if(mat==getChild(0)) {
                        elem.setParent(null);
                    }
                    return elem;
                }
            }
            
            Intpair a=getChild(1).getBounds();
            int numelements=mat.numChildren()-1;
            
            if(a.upper<numelements) {
                // Always safe to trim the right-hand end of the matrix
                ArrayList<ASTNode> newelements=list();
                if(mat==getChild(0)) {
                    mat.detachChildren();
                }
                getChild(1).setParent(null);
                for(int i=1; i<=a.upper; i++) newelements.add(mat.getChild(i));
                return new ElementOne(CompoundMatrix.make(newelements), getChild(1));
            }
	    }
	    
	    return null;
	}
	
	@Override
	public int polarity(int child) {
	    if(child==0) {
	        // The matrix
	        return polarity();
	    }
	    else {
	        // The index expression
	        return 0;
	    }
	}
	
	public Intpair getBounds() {
	    Intpair a = getChild(0).getBounds();
	    return a;
	}
	
	public ArrayList<Intpair> getIntervalSetExp() {
	    return getChild(0).getIntervalSetExp();
    }
	
	public void toFlatzincWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException
	{
	    b.append("constraint array_var_int_element(");   // Could case split here for constant arrays using array_int_element -- Also there may be a bool version.
	    getChild(1).toFlatzinc(b, false);
	    b.append(", ");
	    getChild(0).toFlatzinc(b, false);
	    b.append(", ");
	    aux.toFlatzinc(b, false);
	    b.append(");");
	}
	
	//  Not flattened -- treat as element = true, meaning that the contents of
	//  the matrix must be Boolean.
	@Override
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException
	{
	    b.append("constraint array_var_bool_element(");
	    getChild(1).toFlatzinc(b, false);
	    b.append(", ");
	    getChild(0).toFlatzinc(b, true);
	    b.append(", ");
	    b.append("true");
	    b.append(");");
	}
	
	public void toMinizinc(StringBuilder b,  boolean bool_context) {
	    b.append("(");
	    getChild(0).toMinizinc(b, bool_context);
	    b.append("[");
	    getChild(1).toMinizinc(b, bool_context);
	    b.append("])");
	}
	
	@Override
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
	    assert bool_context;
	    assert this.isRelation();
	    this.toMinionWithAuxVar(b, new BooleanConstant(true));
	}
	
	public void toMinionWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException
	{
	    // Might need to use an element rather than watchelement.
	    if(CmdFlags.getUseBoundVars() && 
	        (aux.exceedsBoundThreshold() || getChild(0).exceedsBoundThreshold() || getChild(1).exceedsBoundThreshold() )) {
	        b.append("element_one(");
	    }
	    else {
	        b.append("watchelement_one(");
	    }
	    
	    getChild(0).toMinion(b, false);
	    b.append(", ");
	    getChild(1).toMinion(b, false);
	    b.append(", ");
	    aux.toMinion(b, false);
	    b.append(")");
	}
}
