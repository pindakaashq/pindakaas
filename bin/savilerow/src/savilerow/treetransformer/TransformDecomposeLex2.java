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

import java.util.ArrayList;

import savilerow.expression.*;
import savilerow.model.Model;

// Decomposition of lex constraints -- this version factors out common parts -- i.e. AC-CSE by hand. 

public class TransformDecomposeLex2 extends TreeTransformerBottomUp
{
    public TransformDecomposeLex2(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    // Decompose Lex constraints for SAT output. 
        if(curnode instanceof LexLess || curnode instanceof LexLessEqual) {
            return decompLex(m, curnode);
        }
        return null;
    }
    
    public static NodeReplacement decompLex(Model m, ASTNode curnode) {
        ASTNode matrix1 = curnode.getChild(0);
        ASTNode matrix2 = curnode.getChild(1);
        
        assert matrix1 instanceof CompoundMatrix && matrix2 instanceof CompoundMatrix;
        
        // Assume the matrix is more than one element long. Otherwise would have been simplified away. 
        ArrayList<ASTNode> newcts=new ArrayList<ASTNode>();
        ArrayList<ASTNode> newcts_root=new ArrayList<ASTNode>();
        
        // At position i, we need to have the boolean variable representing x1 != y1 ... x(i-1) != y(i-1).
        // Starts false. 
        ASTNode curbool=new BooleanConstant(false);
        
        for (int i=1; i < matrix1.numChildren(); i++) {
            
            // Either there is a not-equal pair to the left, or m1[i] <= m2[i]
            if(i<matrix1.numChildren()-1 || curnode instanceof LexLessEqual) {
                newcts.add(new Or(curbool, new LessEqual(matrix1.getChild(i), matrix2.getChild(i))));
            }
            else {
                newcts.add(new Or(curbool, new Less(matrix1.getChild(i), matrix2.getChild(i))));
            }
            
            if(i<matrix1.numChildren()-1) {
                // If not last, make new bool var. 
                ASTNode toreify=new Or(curbool, new AllDifferent(matrix1.getChild(i), matrix2.getChild(i)));
                ASTNode auxvar=m.global_symbols.newAuxHelper(toreify);
                ASTNode flatcon=new ToVariable(toreify, auxvar);
                newcts_root.add(flatcon);
                curbool=auxvar;
            }
        }
        
        return new NodeReplacement(new And(newcts), null, new And(newcts_root));
    }
}

