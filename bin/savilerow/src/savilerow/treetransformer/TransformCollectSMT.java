package savilerow.treetransformer;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2017 Peter Nightingale
    
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

//  Collect all variables that need a direct encoding (in addition to the order encoding).

public class TransformCollectSMT extends TreeTransformerBottomUpNoWrapper
{
    public TransformCollectSMT(Model _m) {
        super(_m);
    }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof Identifier) {

            if (!curnode.isRelation() && curnode.willSMTEncode()) {
                // If the variable appears somewhere as an integer, mark that we need the integer encoding
                // If using bit vectors mark as a bit vector
                if (CmdFlags.getUseBV()) {

                    m.global_symbols.markAsBitVector(curnode.toString());
                }
                else {

                    m.global_symbols.markAsInteger(curnode.toString());
                }
            }
            else {
                // If the variable appears somewhere as a boolean, mark that we need the boolean encoding
                // Special case for when curnode.isRelation() -> always encode as boolean
                m.global_symbols.markAsBoolean(curnode.toString());
                if (!curnode.isRelation() && CmdFlags.getUseIDL()) { m.global_symbols.markAsInteger(curnode.toString()); }
            }
        }
        return null;
    }
}

