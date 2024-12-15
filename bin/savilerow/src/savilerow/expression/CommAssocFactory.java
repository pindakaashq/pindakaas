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

public class CommAssocFactory {
    public static ASTNode makeCommAssoc(String op, ArrayList<ASTNode> args, ArrayList<Long> weights)
	{
	    // Numerical comparisons
        if(op.equals("/\\"))
        {
            assert weights==null;
            return new And(args);
        }
        else if(op.equals("\\/"))
        {
            assert weights==null;
            return new Or(args);
        }
        else if(op.equals("+"))
        {
            assert weights!=null;
            return new WeightedSum(args, weights);
        }
        else if(op.equals("*"))
        {
            assert weights==null;
            return new Times(args);
        }
        else if(op.equals("xor")) {
            assert weights==null;
            return new Xor(args);
        }
        else
        {
            System.out.println("Unsupported commutative associative operator:"+op);
            return null;
        }
	}
}

