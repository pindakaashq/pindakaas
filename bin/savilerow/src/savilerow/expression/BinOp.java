package savilerow.expression;
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

import savilerow.CmdFlags;
import savilerow.model.SymbolTable;

/* =============================================================================
 Base class for the binary operators e.g. Plus, Times
==============================================================================*/

abstract public class BinOp extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    public BinOp(ASTNode l, ASTNode r) {
		super(l,r);
	}
	
	public String toString()
	{
	    return "("+getChild(0)+" "+getClass().getName()+" "+getChild(1)+")";
	}
	
	//  Assume here that it is a numerical binary operator (that takes booleans by casting). Subclasses such as Intersect, InSet will need to override this method.
	public boolean typecheck(SymbolTable st) {
	    for(int i=0; i<2; i++) {
	        if(!getChild(i).typecheck(st)) return false;
	        if(getChild(i).getDimension()>0) {
	            CmdFlags.println("ERROR: Unexpected matrix in binary numerical/logical operator: "+this);
	            return false;
	        }
	        if(getChild(i).isSet()) {
	            CmdFlags.println("ERROR: Unexpected set in binary numerical/logical operator: "+this);
	            return false;
	        }
        }
        return true;
    }
	
	/// Factory method.
	// "+", "-", "/", "*", "**", "%", "\/", "/\", "=>", "<=>", "=", "!=", "<=", "<", ">=", ">", "<lex", "<=lex", ">lex", ">=lex" "in"
    
	// Flips some operators round. > and >= for example, are represented as < and <=
	public static ASTNode make(ASTNode l, String op, ASTNode r) {
	    return makeBinOp(op, l, r);
	}
	
	public static ASTNode makeBinOp(String op, ASTNode operandLeft, ASTNode operandRight)
	{
	    // Numerical comparisons
        if(op.equals("="))
        {
            return new Equals(operandLeft, operandRight);
        }
        else if(op.equals("!="))
        {
            return new NotEqual(operandLeft, operandRight);
        }
        else if(op.equals("<="))
        {
            return new LessEqual(operandLeft, operandRight);
        }
        else if(op.equals("<"))
        {
            return new Less(operandLeft, operandRight);
        }
        else if(op.equals(">="))
        {
            return new LessEqual(operandRight, operandLeft);
        }
        else if(op.equals(">"))
        {
            return new Less(operandRight, operandLeft);
        }
        
        // Vector comparisons
        else if(op.equals("<=lex"))
        {
            return new LexLessEqual(operandLeft, operandRight);
        }
        else if(op.equals("<lex"))
        {
            return new LexLess(operandLeft, operandRight);
        }
        else if(op.equals(">=lex"))
        {
            return new LexLessEqual(operandRight, operandLeft);
        }
        else if(op.equals(">lex"))
        {
            return new LexLess(operandRight, operandLeft);
        }
        
        // In set
        else if(op.equals("in")) {
            return new InSet(operandLeft, operandRight);
        }
        
        // Numerical operators.
        else if(op.equals("+"))
        {
            ArrayList<Long> w=new ArrayList<Long>();
            w.add(1L); w.add(1L);
            ArrayList<ASTNode> ch=new ArrayList<ASTNode>();
            ch.add(operandLeft); ch.add(operandRight);
            return new WeightedSum(ch, w);
        }
        else if(op.equals("-"))
        {   // Might be numerical or set minus.
            if(operandLeft.isSet() || operandRight.isSet()) {
                return new SetDifference(operandLeft, operandRight);
            }
            ArrayList<Long> w=new ArrayList<Long>();
            w.add(1L); w.add(-1L);
            ArrayList<ASTNode> ch=new ArrayList<ASTNode>();
            ch.add(operandLeft); ch.add(operandRight);
            return new WeightedSum(ch, w);
        }
        else if(op.equals("/"))
        {
            return new Divide(operandLeft, operandRight);
        }
        else if(op.equals("*"))
        {
            return new Times(operandLeft, operandRight);
        }
        else if(op.equals("**") )
        {
            return new Power(operandLeft, operandRight);
        }
        else if(op.equals("%"))
        {
            return new Mod(operandLeft, operandRight);
        }
        
        // Logical operators
        else if(op.equals("/\\"))
        {
            return new And(operandLeft, operandRight);
        }
        else if(op.equals("\\/"))
        {
            return new Or(operandLeft, operandRight);
        }
        else if(op.equals("xor"))
        {
            return new Xor(operandLeft, operandRight);
        }
        else if(op.equals("=>") || op.equals("->"))
        {
            return new Implies(operandLeft, operandRight);
        }
        else if(op.equals("<=>") || op.equals("<->"))
        {
            return new Iff(operandLeft, operandRight);
        }
        // Set operators.
        else if(op.equals("union"))
        {
            return new Union(operandLeft, operandRight);
        }
        else if(op.equals("intersect"))
        {
            return new Intersect(operandLeft, operandRight);
        }
        else if(op.equals("subsetEq")) {
            return new SubsetEq(operandLeft, operandRight);
        }
        else if(op.equals("subset")) {
            return new Subset(operandLeft, operandRight);
        }
        else if(op.equals("supsetEq")) {
            return new SubsetEq(operandRight, operandLeft);
        }
        else if(op.equals("supset")) {
            return new Subset(operandRight, operandLeft);
        }
        else
        {
            System.out.println("Unsupported binary operator:"+op);
            return null;
        }
	}
}