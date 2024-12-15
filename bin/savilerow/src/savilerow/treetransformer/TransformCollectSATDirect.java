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

import java.util.HashSet;

import savilerow.*;
import savilerow.expression.*;
import savilerow.model.*;

//  Collect all variables that need a direct encoding (in addition to the order encoding).

public class TransformCollectSATDirect extends TreeTransformerBottomUpNoWrapper
{
    public TransformCollectSATDirect(Model _m) {
        super(_m);
        vars=new HashSet<String>();
    }
    
    private HashSet<String> vars;   // Collect all variables mentioned in constraints. 
    
    protected NodeReplacement processNode(ASTNode curnode)
    {
        if(curnode instanceof Identifier) {
            vars.add(curnode.toString());
            
            if(!curnode.isRelation() && (!CmdFlags.getSMTtrans() || !curnode.willSMTEncode())) {
                //  For non-bool vars, mark as order- or direct-encoded. 
                //  Bool vars automatically have both.
                ASTNode mapfree=curnode;
                // lift above mappers
                // Does not take account of constraints containing CompoundMatrix -- however these are decomposed (allDiff, GCC)
                while(mapfree.getParent() instanceof MultiplyMapper || mapfree.getParent() instanceof ShiftMapper) {
                    mapfree=mapfree.getParent();
                }
                
                ASTNode p=mapfree.getParent();
                
                if(p instanceof LessEqual || p instanceof Less) {
                    ///  LessEqual and Less use the order encoding. 
                    m.global_symbols.markAsOrderSAT(curnode.toString());
                }
                else if(p instanceof WeightedSum) {
                    ///  check if its an AMO, and whether the AMO encoding is one that uses the direct variables.
                    if(Sat.eligibleAMO(p) && CmdFlags.sat_amo_encoding!=AMOEnc.TREE) {
                        m.global_symbols.markAsDirectSAT(curnode.toString());
                    }
                    else {
                        m.global_symbols.markAsOrderSAT(curnode.toString());
                    }
                }
                else if(p instanceof Minimising || p instanceof Maximising) {
                    m.global_symbols.markAsOrderSAT(curnode.toString());
                }
                else {
                    //  All other constraints (and MaxSATObjective) use direct encoding.
                    m.global_symbols.markAsDirectSAT(curnode.toString());
                }
            }
        }
        return null;
    }
    
    public HashSet<String> getVarsInConstraints() {
        return vars;
    }
}

