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

//  More efficient substitution for the specific case of replacing all FromSolution functions.

public class TransformSubInSolution extends TreeTransformerBottomUpNoWrapper
{
    HashMap<String, ASTNode> sol;
    public TransformSubInSolution(HashMap<String, ASTNode> _sol) {
        super(null);
        sol=_sol;
    }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof FromSolution) {
            String name=((FromSolution)curnode).name;
            return new NodeReplacement(sol.get(name));
        }
        return null;
    }
}

