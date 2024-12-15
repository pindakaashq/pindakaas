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
import savilerow.model.Model;

// Flatten any boolean expressions (such as x=a for some integer variable x and value a) contained in a sum.
// This is to enable AMO detection. 

public class TransformExtractBoolsInSums extends TreeTransformerBottomUp
{
    boolean propagate;
    public TransformExtractBoolsInSums(Model _m)
    {
        super(_m);
    }
    
    private static HashMap<ASTNode, String> cache = new HashMap<ASTNode, String>();
    public static HashMap<String, ASTNode> inverseCache = new HashMap<String, ASTNode>();
    
    protected NodeReplacement processNode(ASTNode curnode) {
        if(curnode.isRelation() && (curnode.getParent() instanceof WeightedSum) 
            && !(curnode instanceof Identifier) 
            && !(curnode instanceof Negate && curnode.getChild(0) instanceof Identifier))
        {
            if(cache.containsKey(curnode)) {
                //System.out.println("replacing: "+curnode+" with cached: "+cache.get(curnode));
                ASTNode id=new Identifier(m, cache.get(curnode));
                if(m.global_symbols.category.containsKey(cache.get(curnode))) {
                    return new NodeReplacement(id, null, null);
                }
                else {
                    //  Entry cached from previous tailoring pass. 
                    m.global_symbols.newVariable(cache.get(curnode), new BooleanDomainFull(), ASTNode.Auxiliary);
                    ASTNode flatcon=new ToVariable(curnode, id);
                    m.global_symbols.auxVarRepresentsConstraint(id.toString(), curnode.toString());
                    return new NodeReplacement(id, null, flatcon);
                }
            }
            else {
                //  Make a new aux variable
                String auxname=newAuxId();
                m.global_symbols.newVariable(auxname, new BooleanDomainFull(), ASTNode.Auxiliary);
                ASTNode auxvar=new Identifier(m, auxname);
                ASTNode flatcon=new ToVariable(curnode, auxvar);
                m.global_symbols.auxVarRepresentsConstraint(auxvar.toString(), curnode.toString());
                
                //  Update caches and replace current expression.
                cache.put(curnode, auxname);
                inverseCache.put(auxname, curnode);
                //System.out.println("replacing: "+curnode+" with new: "+auxvar);
                return new NodeReplacement(auxvar, null, flatcon);
            }
        }
        return null;
    }
    
    int auxvarcounter=1;
    //  Find unused name for new auxiliary id.
    public String newAuxId() {
        String newname = "amo_detect_aux" + auxvarcounter;
        while (m.global_symbols.category.containsKey(newname)) {
            auxvarcounter++;
            newname = "amo_detect_aux" + auxvarcounter;
        }
        auxvarcounter++;
        return newname;
    }
}
