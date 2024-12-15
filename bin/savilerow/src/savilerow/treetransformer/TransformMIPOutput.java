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

import savilerow.MIP;
import savilerow.expression.*;

// Late rewrites for output to MIP:
//  -- replace x=c with a 0/1 variable
//  -- replace sum toVar x with sum-x = 0
//  -- lift mappers into weighted sum

public class TransformMIPOutput extends TreeTransformerBottomUpNoWrapper
{
    MIP mip;
    public TransformMIPOutput(MIP _mip) {
        super(null);
        mip=_mip;
    }
    
    protected NodeReplacement processNode(ASTNode curnode)
    {
        //   Unary, nested boolean expressions to be replaced with
        //   (sum of) 0/1 vars. 
        
        if(curnode instanceof Equals) {
            ASTNode c0=mip.stripMappers(curnode.getChild(0));
            ASTNode c1=mip.stripMappers(curnode.getChild(1));
            
            //  Replace x=c with one of the 01 variables. 
            if(c0 instanceof Identifier && c1.isConstant()) {
                return new NodeReplacement(mip.get01var(curnode.getChild(0), curnode.getChild(1).getValue()));
            }
            else if(c1 instanceof Identifier && c0.isConstant()) {
                return new NodeReplacement(mip.get01var(curnode.getChild(1), curnode.getChild(0).getValue()));
            }
            //  What if it's top-level?
        }
        
        if(curnode instanceof AllDifferent && !curnode.getParent().inTopAnd()) {
            assert curnode.getChild(0).numChildren()==3;
            ASTNode c0=curnode.getChild(0).getChild(1);
            ASTNode c1=curnode.getChild(0).getChild(2);
            
            //  Replace x=c with one of the 01 variables. 
            if(c0 instanceof Identifier && c1.isConstant()) {
                return new NodeReplacement(mip.negate(mip.get01var(c0, c1.getValue())));
            }
            else if(c1 instanceof Identifier && c0.isConstant()) {
                System.out.println(curnode);   //  Problem is it's a bool variable. 
                return new NodeReplacement(mip.negate(mip.get01var(c1, c0.getValue())));
            }
            // Top-level?
        }
        
        if((curnode instanceof LessEqual || curnode instanceof Less) && !curnode.getParent().inTopAnd()) {
            ASTNode c0=curnode.getChild(0);
            ASTNode c1=curnode.getChild(1);
            
            if(c0 instanceof Identifier && c1.isConstant()) {
                ArrayList<Intpair> dom=c0.getIntervalSetExp();
                ArrayList<Intpair> ct=new ArrayList<>();
                ct.add(new Intpair(Long.MIN_VALUE, c1.getValue()-((curnode instanceof LessEqual)?0:1)));
                dom=Intpair.intersection(dom, ct);
                return new NodeReplacement(mip.inset(curnode, c0, dom));
            }
            else if(c1 instanceof Identifier && c0.isConstant()) {
                ArrayList<Intpair> dom=c1.getIntervalSetExp();
                ArrayList<Intpair> ct=new ArrayList<>();
                ct.add(new Intpair(c0.getValue()+((curnode instanceof LessEqual)?0:1), Long.MAX_VALUE));
                dom=Intpair.intersection(dom, ct);
                return new NodeReplacement(mip.inset(curnode, c1, dom));
            }
            
        }
        
        if(curnode instanceof InSet) {
            ArrayList<Intpair> intervals=curnode.getChild(1).getIntervalSet();
            return new NodeReplacement(mip.inset(curnode, curnode.getChild(0), intervals));
        }
        
        //////////////////////////////////////////////////////////////////////
        //
        //   Top-level constraints. 
        
        if(curnode instanceof ToVariable) {
            //  ToVar with WeightedSum  becomes equality to a constant. 
            if(curnode.getChild(0) instanceof WeightedSum) {
                if(curnode.getChild(1).isConstant()) {
                    return new NodeReplacement(new Equals(curnode.getChild(0), curnode.getChild(1)));
                }
                else {
                    // Shift the variable into the LHS sum.  Relies on Equals simplifier to take constants out of the
                    // sum to the RHS. 
                    ArrayList<ASTNode> terms=curnode.getChild(0).getChildren();
                    ArrayList<Long> coeffs=((WeightedSum)curnode.getChild(0)).getWeights();
                    terms.add(curnode.getChild(1));
                    coeffs.add(-1L);
                    
                    return new NodeReplacement(new Equals(new WeightedSum(terms,coeffs), NumberConstant.make(0)));
                }
            }
        }
        
        //  Should not need this. 
        if(curnode instanceof WeightedSum) {
            //  Check for mappers
            for(int i=0; i<curnode.numChildren(); i++) {
                if(curnode.getChild(i) instanceof MultiplyMapper) {
                    ArrayList<ASTNode> ch=curnode.getChildren();
                    ArrayList<Long> coeff=((WeightedSum)curnode).getWeights();
                    coeff.set(i, coeff.get(i)*ch.get(i).getChild(1).getValue());
                    ch.set(i, ch.get(i).getChild(0));
                    return new NodeReplacement(new WeightedSum(ch, coeff));
                }
                // What about shiftmappers?
            }
        }
        
        //  Disequality (top-level) -- not decomposed. 
        if(curnode instanceof AllDifferent && curnode.getParent().inTopAnd()) {
            assert curnode.getChild(0).numChildren()==3;
            return new NodeReplacement(mip.diseq(curnode.getChild(0).getChild(1), curnode.getChild(0).getChild(2)));
        }
        
        //////////////////////////////////////////////////////////////////////
        //  Deal with ToVariable constraints for basic types:  =, !=, /\, \/
        if(curnode instanceof ToVariable) {
            if(curnode.getChild(0) instanceof Equals) {
                // RHS implies the two expressions are equal.
                ASTNode c1=mip.equal(curnode.getChild(0).getChild(0), curnode.getChild(0).getChild(1), curnode.getChild(1));
                
                // !RHS implies not equal. 
                ASTNode c2=mip.diseq(curnode.getChild(0).getChild(0), curnode.getChild(0).getChild(1), mip.negate(curnode.getChild(1)));
                
                return new NodeReplacement(new And(c1, c2));
            }
            if(curnode.getChild(0) instanceof AllDifferent) {
                assert curnode.getChild(0).getChild(0).numChildren()==3;
                ASTNode a=curnode.getChild(0).getChild(0).getChild(1);
                ASTNode b=curnode.getChild(0).getChild(0).getChild(2);
                
                ASTNode c1=mip.diseq(a, b, curnode.getChild(1));
                
                // !RHS implies equal. 
                ASTNode c2=mip.equal(a, b, mip.negate(curnode.getChild(1)));
                
                return new NodeReplacement(new And(c1, c2));
            }
            if(curnode.getChild(0) instanceof LessEqual) {
                ASTNode a=curnode.getChild(0).getChild(0);
                ASTNode b=curnode.getChild(0).getChild(1);
                
                assert a.isConstant() || b.isConstant();  //  Otherwise would be rewritten by 'move over to one side' rule. 
                
                long k;
                if(a.isConstant()) {
                    //  reverse the LessEqual so that b is the constant. 
                    k=-a.getValue();
                    a=new UnaryMinus(b);
                }
                else {
                    k=b.getValue();
                }
                //  a <= k from here on.
                
                // RHS -> (a <= k)
                ASTNode c1=mip.implyIneq(curnode.getChild(1), a, k);
                
                // !RHS -> -a <= -k-1
                ASTNode c2=mip.implyIneq(mip.negate(curnode.getChild(1)), new UnaryMinus(a), -k-1);
                
                return new NodeReplacement(new And(c1, c2));
            }
            if(curnode.getChild(0) instanceof Or) {
                //  LHS >= RHS   (i.e. when RHS is 1, LHS>=1
                ASTNode lhssum=new WeightedSum(curnode.getChild(0).getChildrenArray());
                ASTNode c1=new LessEqual(NumberConstant.make(0), new WeightedSum(new ASTNode[]{lhssum, curnode.getChild(1)}, new long[]{1, -1}));
                
                //  LHS=0 when RHS=0
                ASTNode c2=mip.implyIneq(mip.negate(curnode.getChild(1)), lhssum, 0);
                return new NodeReplacement(new And(c1, c2));
            }
        }
        
        if(curnode instanceof LessEqual && curnode.getChild(0).getCategory()!=ASTNode.Constant && curnode.getChild(1).getCategory()!=ASTNode.Constant) {
            //  Move over to one side -- always have RHS of <= as the constant. 
            return new NodeReplacement(new LessEqual(
                new WeightedSum(new ASTNode[]{curnode.getChild(0), curnode.getChild(1)}, new long[]{1, -1}),
                NumberConstant.make(0)));
        }
        
        if(curnode instanceof Less && curnode.getChild(0).getCategory()!=ASTNode.Constant && curnode.getChild(1).getCategory()!=ASTNode.Constant) {
            //  Rewrite a<b  as a-b<=-1
            return new NodeReplacement(new LessEqual(
                new WeightedSum(new ASTNode[]{curnode.getChild(0), curnode.getChild(1)}, new long[]{1, -1}),
                NumberConstant.make(-1)));
        }
        
        /////////////////////////////////////////////////////////////////////
        //
        //  Top-level logic constraints
        
        if(curnode instanceof Or && curnode.getParent().inTopAnd()) {
            return new NodeReplacement(new LessEqual(NumberConstant.make(1), new WeightedSum(curnode.getChildrenArray())));
        }
        
        //  Implication
        
        if(curnode instanceof Implies && curnode.getParent().inTopAnd()) {
            return new NodeReplacement(new Or(mip.negate(curnode.getChild(0)), curnode.getChild(1)));
        }
        
        
        
        
        
        return null;
    }
}

