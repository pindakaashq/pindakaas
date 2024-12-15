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

import savilerow.CmdFlags;
import savilerow.model.SymbolTable;

//  e.g. multiStage(currentSize, [10,9,8,7,6,5,4,3,2,1])  specifies a multi-stage
//  problem instance where decision variable currentSize is set to 10 first. 

public class IncomparabilityFunction extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public IncomparabilityFunction(ASTNode a, ASTNode b)
    {
        super(a, b);
        
        //   Set -S0 in effect.  Preserve set of solutions exactly. 
        CmdFlags.setRemoveRedundantVars(false);
        CmdFlags.setAuxNonFunctional(false);
        CmdFlags.setUseVarSymBreaking(false);

        // add 
        CmdFlags.setFindAllSolutions(true);
    }
    
    public ASTNode copy() {
        return new IncomparabilityFunction(getChild(0), getChild(1));
    }
    
    public boolean toFlatten(boolean propagate) { return false; }
    public boolean isRelation() {
        return true;
    }
    
    @Override
    public ASTNode simplify() {
        if(getChild(1) != getChildConst(1)) {
            // hack hack hack
            return new IncomparabilityFunction(getChild(0), getChildConst(1).copy());
        }
        return null;
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        if((!getChild(0).typecheck(st)) || (!getChild(1).typecheck(st))) {
            return false;
        }
        
        if( !getChild(0).isConstant() || !getChild(1).isNumerical()) {
            CmdFlags.typeError("Expected order and function in IncomparabilityFunction.");
            return false;
        }
        return true;
    }
    
    public String toString() {
        return "incomparabilityFunction("+getChild(0)+","+getChild(1)+")";
    }
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        // no output to Minion.
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        // no output to Fzn.
    }
}
