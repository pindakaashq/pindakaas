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

//  Get rid of N-ary times.

public class TransformTimes extends TreeTransformerBottomUpNoWrapper
{
    public TransformTimes(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof Times && curnode.numChildren()!=2)
        {
            ASTNode a=curnode.getChild(0);
            
            for(int i=1; i<curnode.numChildren(); i++) {
                a=new Times(a, curnode.getChild(i));
            }
            return new NodeReplacement(a);
        }
        return null;
    }
}

