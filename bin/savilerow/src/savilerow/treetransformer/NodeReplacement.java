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

import savilerow.expression.ASTNode;

//  Just a container for things that need to be returned from processNode.

public class NodeReplacement {
    public NodeReplacement(ASTNode cur, ASTNode rel, ASTNode cons) {
        current_node=cur;
        rel_context=rel;
        new_constraint=cons;
    }
    
    // Just replace the current node.
    public NodeReplacement(ASTNode cur) {
        current_node=cur;
        rel_context=null;
        new_constraint=null;
    }
    public ASTNode current_node;
    public ASTNode rel_context;
    public ASTNode new_constraint;
}
