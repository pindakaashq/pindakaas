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





import savilerow.expression.*;
import savilerow.model.Model;

// Generic flattener to catch all cases not dealt with by CSE, special-purpose flatteners, etc. 

public class TransformToFlat extends TreeTransformerBottomUp
{
    boolean propagate;
    public TransformToFlat(Model mod, boolean _propagate)
    {
        super(mod);
        propagate=_propagate;
    }
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode.toFlatten(propagate) && (curnode.getParent()==null || !(curnode.getParent() instanceof ToVariable)))  // Needs flattening and not already flat.
	    {
	        ASTNode auxvar=m.global_symbols.newAuxHelper(curnode);
	        ASTNode flatcon=new ToVariable(curnode, auxvar);
            m.global_symbols.auxVarRepresentsConstraint(auxvar.toString(), curnode.toString());
            return new NodeReplacement(auxvar, null, flatcon);
	    }
	    return null;
	}
}
