package savilerow.treetransformer;
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

import savilerow.CmdFlags;
import savilerow.expression.*;
import savilerow.model.Model;

// Generic flattener to catch all cases not dealt with by CSE, special-purpose flatteners, etc. 

public class TransformToFlatSMT extends TreeTransformerBottomUp
{
    public TransformToFlatSMT(Model _m, boolean _propagate) {
        super(_m);
        assert CmdFlags.getSMTtrans();
        assert !_propagate;
    }
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
		if(curnode.toFlatten(false) && (curnode.getParent()==null || !(curnode.getParent() instanceof ToVariable)))  // Needs flattening and not already flat.
	    {
	        if (!shouldFlattenSMT(curnode)) { return null; }
            ASTNode auxvar=m.global_symbols.newAuxHelper(curnode);
	        ASTNode flatcon=new ToVariable(curnode, auxvar);
            m.global_symbols.auxVarRepresentsConstraint(auxvar.toString(), curnode.toString());
            return new NodeReplacement(auxvar, null, flatcon);
	    }
	    return null;
	}
	
    private static boolean shouldFlattenSMT(ASTNode curnode) {
        if (CmdFlags.getUseUF()) { return true; }
        if (CmdFlags.getUseFlat()) { return true; }
        
        //  Rest governs behaviour with nested encoding, IDL/LIA/NIA
        ASTNode p=curnode.getParent();
        if (p instanceof ElementOne || p instanceof SafeElementOne) { return true; }
        if (p instanceof Mapping) {
            return true;
        }
        if (curnode instanceof ElementOne || curnode instanceof SafeElementOne) { return true; }
        if (CmdFlags.getUseLIA() || CmdFlags.getUseIDL()) {
            //  If the parent is an operator not available in LIA or IDL then it (the parent) must be encoded into SAT and
            //  SAT rules of flattening apply. 
            if(!p.willSMTEncode()) {
                return curnode.toFlatten(false);
            }
            
            if (curnode instanceof Divide) { return true; }
            if (curnode instanceof Negate) { return true; }
            if (curnode instanceof UnaryMinus) { return true; }
            if (curnode instanceof Times) { return true; }
            if (curnode instanceof Mod) { return true; }
        }
        if (CmdFlags.getUseIDL()) {
            if (curnode instanceof ShiftMapper) { return true; }
            if (curnode instanceof Absolute) { return true; }
            if (curnode instanceof WeightedSum) { return true; }
            if (curnode instanceof Equals) { return true; }
            if (curnode instanceof Less) { return true; }
            if (curnode instanceof LessEqual) { return true; }
            if (curnode instanceof ToVariable) { return true; }
            if (curnode instanceof And) { return true; }
            if (curnode instanceof AllDifferent) { return true; }
            if (curnode instanceof InSet) { return true; }
        }
        
        return false;
    }
}
