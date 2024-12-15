package savilerow.eprimeparser;
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
import java.util.HashMap;
import java.util.Map;

import savilerow.expression.*;

/* An implementation of Dijkstra's shunting-yard algorithm to produce a tree
from a list of part expressions and binary operators. 

*/

//String[] ops={"+", "-", "/", "*", "^", "%", "\\/", "/\\", "=>", "<=>", "=", "!=", "<=", "<", ">=", ">", "<lex", "<=lex", ">lex", ">=lex"};
//    binops = new HashSet(Arrays.asList(ops));

class ShuntingYard
{
    private HashMap<String, Integer> precedence;
    private HashMap<String, Boolean> left_associative;
    
    ShuntingYard()
    {
        precedence=new HashMap<String, Integer>();
        left_associative=new HashMap<String, Boolean>();
        
        // Exponentiation
        precedence.put("^", 11);
        precedence.put("**", 11);
        
        // These three are equal precedence left-associative
        precedence.put("*", 10);
        precedence.put("/", 10);
        precedence.put("%", 10);
        
        // Addition, subtraction
        precedence.put("+", 1);
        precedence.put("-", 1);
        
        // Numerical Comparisons
        precedence.put("=", 0);
        precedence.put("!=", 0);
        precedence.put("<=", 0);
        precedence.put("<", 0);
        precedence.put(">=", 0);
        precedence.put(">", 0);
        
        // Vector comparisons
        precedence.put("<lex", 0);
        precedence.put("<=lex", 0);
        precedence.put(">lex", 0);
        precedence.put(">=lex", 0);
        
        // In set
        precedence.put("in", 0);
        
        // Boolean operators
        precedence.put("/\\", -1);   // And has higher precedence than or.
        precedence.put("xor", -2);   // XOR between and, or following conventions of C and Java (for bitwise operators &, ^, | )
        precedence.put("\\/", -3);
        
        precedence.put("=>", -4);
        precedence.put("<=>", -4);
        precedence.put("->", -4);
        precedence.put("<->", -4);
        
        // Set operations -- NOT mixed with any of the above except "-" is used for both sets and integers. 
        precedence.put("intersect", 2);
        precedence.put("union", 1);
        precedence.put("subsetEq", 0);
        
        // Build left_associative from precedence
        for (Map.Entry<String, Integer> entry: precedence.entrySet()) {
            left_associative.put(entry.getKey(), true);
        }
        left_associative.put("^", false); // Exponentiation is right-associative. i.e. 2^3^4 = 2^(3^4)
        left_associative.put("**", false);
    }
    
    public ASTNode convertToTree(ArrayList<ASTNode> input)
    {
        return evaluate(toRPN(input));
    }
    
    /* =========================================================================
    Implements part of the shunting-yard algorithm to convert the infix input 
    into reverse Polish notation output. 
    We only have left-associative and right-associative binary operators, 
    no brackets or anything else, therefore only two rules are implemented.
    ========================================================================= */
    
    private ArrayList<ASTNode> toRPN(ArrayList<ASTNode> input)
    {
        ArrayList<ASTNode> output=new ArrayList<ASTNode>();  // Output queue
        ArrayList<ASTNode> ops=new ArrayList<ASTNode>();     // Operator stack
        
        for(int i=0; i<input.size(); i++)
        {
            ASTNode tok=input.get(i);
            if(!(tok instanceof BinOpPlaceholder))
            {   // If the token is not an operator
                output.add(tok);
            }
            else
            {   // tok is a BinOp.
                while(ops.size()>0)
                {
                    ASTNode o2=ops.get(ops.size()-1);
                    String tok_name=((BinOpPlaceholder)tok).op;
                    // Left-associative rule.
                    if(left_associative.get(tok_name) && 
                        (precedence.get(tok_name) <= precedence.get(((BinOpPlaceholder)o2).op)))
                    {   // o2 has higher or equal precedence. 
                        // take o2 off the ops stack and add to the output.
                        output.add(o2);
                        ops.remove(ops.size()-1);
                    }
                    // Right-associative rule.
                    else if(!left_associative.get(tok_name) && 
                        (precedence.get(tok_name) < precedence.get(((BinOpPlaceholder)o2).op)))
                    {
                        output.add(o2);
                        ops.remove(ops.size()-1);
                    }
                    else
                    {
                        break;
                    }
                }
                ops.add(tok);
            }
        }
        
        // Finished reading input, now pop the remaining BinOps from the 
        // ops stack to the output.
        while(ops.size()>0)
        {
            output.add(ops.get(ops.size()-1));
            ops.remove(ops.size()-1);
        }
        return output;
    }
    
    /* =========================================================================
    Implements the postfix stack evaluation algorithm to create a tree of 
    binary operator nodes. 
    ========================================================================  */
    private ASTNode evaluate(ArrayList<ASTNode> input)
    {
        
        ArrayList<ASTNode> stack=new ArrayList<ASTNode>();
        for(int i=0; i<input.size(); i++)
        {
            ASTNode tok=input.get(i);
            if(tok instanceof BinOpPlaceholder)
            {
                ASTNode operandLeft=stack.get(stack.size()-2);
                ASTNode operandRight=stack.get(stack.size()-1);
                stack.remove(stack.size()-1); stack.remove(stack.size()-1); 
                
                // Horrible switch here. 
                String op=((BinOpPlaceholder)tok).op;
                ASTNode a= BinOp.makeBinOp(op, operandLeft, operandRight);
                stack.add(a);
            }
            else
            {
                stack.add(tok);
            }
        }
        assert stack.size()==1;
        return stack.get(0);
    }
    
}
