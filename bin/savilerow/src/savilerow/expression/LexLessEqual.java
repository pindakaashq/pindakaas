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



import java.io.BufferedWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import savilerow.CmdFlags;

public class LexLessEqual extends MatrixBinOp
{
    public static final long serialVersionUID = 1L;
	public LexLessEqual(ASTNode l, ASTNode r)
	{
		super(l, r);
	}
	
	public ASTNode copy()
	{
	    return new LexLessEqual(getChild(0), getChild(1));
	}
	public boolean isRelation(){return true;}
	public boolean strongProp() {
        return getChild(0).strongProp() && getChild(1).strongProp();
    }
    
	@Override
	public ASTNode simplify() {
	    ASTNode mleft=getChildConst(0);
	    ASTNode mright=getChildConst(1);
	    if( (mleft instanceof CompoundMatrix || mleft instanceof EmptyMatrix) && 
	        (mright instanceof CompoundMatrix || mright instanceof EmptyMatrix) ) {
	        ArrayList<ASTNode> left=getChild(0).getChildren(1);
	        ArrayList<ASTNode> right=getChild(1).getChildren(1);
	        
	        // Deal with unequal length first.
	        if(left.size()<right.size()) {
	            // If they are equal up to the size of left, that will satisfy the constraint. 
	            
	            while(right.size()>left.size()) right.remove(right.size()-1);  // Trim to same size. 
	            if(mleft==getChild(0)) {
	                for(int i=0; i<left.size(); i++) left.get(i).setParent(null);    /// No copy of either left or right.
	            }
	            if(mright==getChild(1)) {
	                for(int i=0; i<right.size(); i++) right.get(i).setParent(null);
	            }
	            return new LexLessEqual(CompoundMatrix.make(left), CompoundMatrix.make(right));
	        }
	        if(left.size()>right.size()) {
	            // If they are equal up to the size of right, that will violate the constraint.
	            // Rewrite into a LexLess.
	            while(left.size()>right.size()) left.remove(left.size()-1);  // Trim to same size.
	            if(mleft==getChild(0)) {
	                for(int i=0; i<left.size(); i++) left.get(i).setParent(null);    /// No copy of either left or right.
	            }
	            if(mright==getChild(1)) {
	                for(int i=0; i<right.size(); i++) right.get(i).setParent(null);
	            }
	            return new LexLess(CompoundMatrix.make(left), CompoundMatrix.make(right));
	        }
	        
	        boolean changed=false;
	        
	        // Now trim out all equal entries. 
            int location = 0;
            while(location < left.size()) {
                if(left.get(location).equals(right.get(location))) {
                    left.remove(location);
                    right.remove(location);
                    changed=true;
                }
                else {
                    location++;
                }
            }

            // -A < -B is equivalent to B < A
            for(int i = 0; i < left.size(); ++i) {
                if(left.get(i) instanceof UnaryMinus && right.get(i) instanceof UnaryMinus) {
                    ASTNode temp = left.get(i).getChild(0);
                    left.set(i, right.get(i).getChild(0));
                    right.set(i, temp);
                    changed=true;
                }
            }

            changed = changed || furtherSimplify(left, right);
            if(changed) {
	            if(mleft==getChild(0)) {
	                for(int i=0; i<left.size(); i++) left.get(i).setParent(null);    /// No copy of either left or right.
	            }
	            if(mright==getChild(1)) {
	                for(int i=0; i<right.size(); i++) right.get(i).setParent(null);
	            }
	            return new LexLessEqual(CompoundMatrix.make(left), CompoundMatrix.make(right));
	        }
	        
	        // Trim from the right-hand side. 
	        while(left.size()>=1) {
	            Intpair leftbnds=left.get(left.size()-1).getBounds();
	            Intpair rightbnds=right.get(right.size()-1).getBounds();
	            
	            // To satisfy the LexLessEqual constraint, the rightmost element must
	            // be less or equal.  Trim off ones that are greater. 
	            if(leftbnds.lower > rightbnds.upper) {
	                left.remove(left.size()-1);
	                right.remove(right.size()-1);
	                changed=true;
	            }
	            else {
	                break;
	            }
	        }
	        
	        if(changed) {
	            // If changed by trimming the right-hand side, the two vectors cannot be
	            // equal. Rewrite to a strict less-than. 
	            if(mleft==getChild(0)) {
	                for(int i=0; i<left.size(); i++) left.get(i).setParent(null);    /// No copy of either left or right.
	            }
	            if(mright==getChild(1)) {
	                for(int i=0; i<right.size(); i++) right.get(i).setParent(null);
	            }
	            return new LexLess(CompoundMatrix.make(left), CompoundMatrix.make(right));
	        }
	        
	        if(left.size()==0 && right.size()==0) {
	            // Since this is less-equal, the constraint is satisfied. 
	            return new BooleanConstant(true);
	        }
	        
	        // Finally, check if the leftmost elements are disjoint and lessthan. 
	        
	        Intpair leftbnds=left.get(0).getBounds();
	        Intpair rightbnds=right.get(0).getBounds();
	        
	        if(leftbnds.upper<rightbnds.lower) {
	            // Guaranteed satisfied by the first element. 
	            return new BooleanConstant(true);
	        }
	        
	        if(leftbnds.lower>rightbnds.upper) {
	            // Guaranteed violated by first element. 
	            return new BooleanConstant(false);
	        }
	        
	        // Strength reduction to numerical <=
	        if(left.size()==1) {
	            return new LessEqual(left.get(0), right.get(0));
	        }
	        
	        if(changed) {
	            if(mleft==getChild(0)) {
	                for(int i=0; i<left.size(); i++) left.get(i).setParent(null);    /// No copy of either left or right.
	            }
	            if(mright==getChild(1)) {
	                for(int i=0; i<right.size(); i++) right.get(i).setParent(null);
	            }
	            return new LexLessEqual(CompoundMatrix.make(left), CompoundMatrix.make(right));
	        }
	    }
	    return null;
	}
	
	@Override
	public int polarity(int child) {
	    return polarity()*((child==0)? -1 : 1);
	}
	
	public boolean furtherSimplify(ArrayList<ASTNode> left, ArrayList<ASTNode> right) {
	    if (left.size() != right.size()) {
	        throw new IllegalArgumentException("Expecting two ArrayLists of the same length");
	    }
	    boolean changed = false;
	    Map<ASTNode, Set<ASTNode>> containingSets = new HashMap<ASTNode, Set<ASTNode>>(); // mapping from variable to the set containing that variable
	    
	    int i = 0;
	    
	    while (i < left.size()) {
	        Set<ASTNode> leftContainer  = containingSets.get(left.get(i));
	        Set<ASTNode> rightContainer = containingSets.get(right.get(i));
	        if (leftContainer == null) {
	            leftContainer = new HashSet<ASTNode>();
	            leftContainer.add(left.get(i));
	            containingSets.put(left.get(i), leftContainer);
	        }
	        if (rightContainer == null) {
	            rightContainer = new HashSet<ASTNode>();
	            rightContainer.add(right.get(i));
	            containingSets.put(right.get(i), rightContainer);
	        }

	        if (leftContainer.contains(right.get(i)) || rightContainer.contains(left.get(i))) {
	            left.remove(i);
	            right.remove(i);
	            changed = true;
	        } else {
	            //moving always happens left to right so swap references if necessary 
	            if (leftContainer.size() > rightContainer.size()) {
	                //swap sets
	                Set<ASTNode> tempContainer = leftContainer;
	                leftContainer = rightContainer;
	                rightContainer = tempContainer;
	            }

	            //move all from leftset to right set
	            rightContainer.addAll(leftContainer);
	            for (ASTNode n: leftContainer) {
	                containingSets.put(n, rightContainer);
	            }
	            i++;
	        }
	    }
	    return changed;
	}
	
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    assert bool_context;
	    b.append("lexleq(");
	    getChild(0).toMinion(b, false);
	    b.append(",");
	    getChild(1).toMinion(b, false);
	    b.append(")");
	}
	public String toString() {
	    return "("+getChild(0)+" <=lex "+getChild(1)+")";
	}
	/*  Experiment with the boolean lex ordering constraint. 
	public void toFlatzinc(BufferedWriter b, boolean bool_context)
	{
	    boolean boolmatrices=getChild(0).isRelation() && getChild(1).isRelation();
	    if(boolmatrices) {
	        b.append("constraint array_bool_lq(");
	    }
	    else {
	        b.append("constraint array_int_lq(");
	    }
	    getChild(0).toFlatzinc(b, boolmatrices);
	    b.append(",");
	    getChild(1).toFlatzinc(b, boolmatrices);
	    b.append(");");
	}*/
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
	    if(CmdFlags.getGecodetrans()) {
	        b.append("constraint array_int_lq(");
	    }
	    else {
	        // Chuffed
	        b.append("constraint lex_lesseq_int(");
	    }
	    getChild(0).toFlatzinc(b, false);
	    b.append(",");
	    getChild(1).toFlatzinc(b, false);
	    b.append(");");
	}
	public void toMinizinc(StringBuilder b, boolean bool_context)
	{
	    b.append("lex_lesseq(");
	    getChild(0).toMinizinc(b, false);
	    b.append(",");
	    getChild(1).toMinizinc(b, false);
	    b.append(")");
	}
}