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




import java.util.HashMap;

import savilerow.expression.*;

public class SubstituteAllValues extends TreeTransformerBottomUpNoWrapper
{
    HashMap<String, Long> subs;
    
    public SubstituteAllValues(HashMap<String, Long> s)
    {
        super(null);
        subs=s;
    }
    
	protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof Identifier) {
	        String idname=curnode.toString();
	        if(subs.containsKey(idname)) {
	            if(curnode.isRelation()) {
	                return new NodeReplacement(new BooleanConstant(subs.get(idname)==1?true:false));
	            }
	            else {
	                return new NodeReplacement(NumberConstant.make(subs.get(idname)));
	            }
	        }
	    }
	    return null;
	}
}

