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

import savilerow.*;
import savilerow.expression.*;
import savilerow.model.Model;

//   Convert sum constraints to AMOPBs. 

public class TransformSumToAMOPB extends TreeTransformerBottomUp
{
    public TransformSumToAMOPB(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
    {
        return processNode(curnode, false, false);
    }
    
    protected NodeReplacement processNode(ASTNode curnode, boolean useEquality, boolean alwaysTransform) {
        ArrayList<ASTNode> ch=null;
        ArrayList<Long> wts=null;
        long cmp=0L;
        long encoding=-1L;
        boolean equality=false;
        
        //  Catch all cases of a sum in a binop.
        if(curnode instanceof ToVariable && curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant()) {
            ch=curnode.getChild(0).getChildren();
            wts=((WeightedSum)curnode.getChild(0)).getWeights();
            
            cmp=curnode.getChild(1).getValue();
            equality=true;
        }
        
        if(curnode instanceof Less && curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant()) {
            ch=curnode.getChild(0).getChildren();
            wts=((WeightedSum)curnode.getChild(0)).getWeights();
            
            cmp=curnode.getChild(1).getValue()-1;  // convert to <=
        }
        
        if(curnode instanceof LessEqual && curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant()) {
            ch=curnode.getChild(0).getChildren();
            wts=((WeightedSum)curnode.getChild(0)).getWeights();
            
            cmp=curnode.getChild(1).getValue();
        }
        
        if(curnode instanceof Less && curnode.getChild(1) instanceof WeightedSum && curnode.getChild(0).isConstant()) {
            // k < sum  becomes  -sum < -k  becomes  -sum <= -k-1
            ch=curnode.getChild(1).getChildren();
            wts=((WeightedSum)curnode.getChild(1)).getWeights();
            for(int i=0; i<wts.size(); i++) {
                wts.set(i, -wts.get(i));  // negate the weights
            }
            
            cmp=-curnode.getChild(0).getValue()-1;
        }
        
        if(curnode instanceof LessEqual && curnode.getChild(1) instanceof WeightedSum && curnode.getChild(0).isConstant()) {
            // k <= sum  becomes  -sum <= -k 
            ch=curnode.getChild(1).getChildren();
            wts=((WeightedSum)curnode.getChild(1)).getWeights();
            for(int i=0; i<wts.size(); i++) {
                wts.set(i, -wts.get(i));  // negate the weights
            }
            
            cmp=-curnode.getChild(0).getValue();
        }
        
        if(CmdFlags.amo_detect_override && curnode instanceof AMOPB) {
            //  Override the existing AMO groups in the AMOPB ct with auto-detected AMO groups (if -amo-detect is on). 
            // Loses existing amo groups but keeps encoding. 
            encoding=curnode.getChild(2).getValue();
            ch=new ArrayList<ASTNode>();
            wts=new ArrayList<Long>();
            ASTNode mat=curnode.getChild(0);
            for(int i=1; i<mat.numChildren(); i++) {
                ch.addAll(mat.getChild(i).getChild(2).getChildren(1));
                
                ASTNode coeffs=mat.getChild(i).getChild(1);
                for(int j=1; j<coeffs.numChildren(); j++) {
                    wts.add(coeffs.getChild(j).getValue());
                }
            }
            cmp=curnode.getChild(1).getValue();
            equality=(curnode.getChild(3).getValue()==1);
        }
        
        if(ch==null) {
            return null;
        }
        
        //  Avoid non-top-level cts, which will fall back to the tree encoding. 
        if(curnode.getParent()!=null && !curnode.getParent().inTopAnd()) {
            if( (!CmdFlags.use_polarity) || curnode.polarity()!=1) {
                return null;
            }
        }
        
        //  Is it entirely boolean
        boolean allBool=true;
        for(int i=0; i<ch.size(); i++) {
            if(!ch.get(i).isRelation()) {
                allBool=false;
                break;
            }
        }
        
        //  Check command-line flags.
        if((allBool && CmdFlags.getSatPBEnc()==SumEnc.TREE && !alwaysTransform)
            || (!allBool && CmdFlags.getSatSumEnc()==SumEnc.TREE && !alwaysTransform)) {
            return null;
        }
        
        if(encoding==-1) {
            SumEnc e = allBool ? CmdFlags.getSatPBEnc() : CmdFlags.getSatSumEnc();
            encoding=(e==SumEnc.MDD)? 1 : (e==SumEnc.GPW? 2 : (e==SumEnc.SWC? 3 : (e==SumEnc.GGT? 4 : (e==SumEnc.RGGT ? 5 : (e==SumEnc.GGTH ? 6 : (e==SumEnc.GMTO ? 7 : (e==SumEnc.LPW ? 8 : 9 )))))));
        }
        //  Flip any negative weights of non-boolean variables.
        // Shift any terms that go below 0 -- non-bool expressions only -- guaranteed by lower bound <0. 
        for(int i=0; i<ch.size(); i++) {
            if(! (ch.get(i).isConstant())) {
                Intpair bnds=ch.get(i).getBounds();
                if((bnds.lower<0 || bnds.upper>1) && wts.get(i)<0) {
                    wts.set(i, -wts.get(i));
                    ch.set(i, new MultiplyMapper(ch.get(i), NumberConstant.make(-1)));
                }
                if(bnds.lower<0) {
                    ch.set(i, new ShiftMapper(ch.get(i), NumberConstant.make(-bnds.lower)));
                    cmp=cmp+(-bnds.lower)*wts.get(i);
                }
            }
        }
        
        //  If it's an equality, break it up into inequalities unless we're using the NEWTREE encoding. 
        //  Then recursive calls to do the transformation. 
        if(curnode instanceof ToVariable && !useEquality) {
            ASTNode c1=new LessEqual(curnode.getChild(0), curnode.getChild(1)); 
            ASTNode c2=new LessEqual(curnode.getChild(1), curnode.getChild(0));
            
            NodeReplacement nr1=processNode(c1, useEquality, alwaysTransform);
            NodeReplacement nr2=processNode(c2, useEquality, alwaysTransform);
            
            return new NodeReplacement(new And(nr1.current_node, nr2.current_node), null, new And(nr1.new_constraint, nr2.new_constraint));
        }
        
        //  Parameters of the AMOPB constraint.
        ArrayList<ASTNode> amoproducts=new ArrayList<ASTNode>();
        
        for(int i=0; i<ch.size(); i++) {
            if(ch.get(i)==null) {
                continue;   //  This element has been deleted
            }
            
            if(ch.get(i).isConstant()) {
                long val=ch.get(i).getValue()*wts.get(i);
                cmp -= val;  //  Move to the other side of the <=.
            }
            else {
                ArrayList<ASTNode> coeffs_onevar=new ArrayList<ASTNode>();
                ArrayList<ASTNode> bools_onevar=new ArrayList<ASTNode>();
                
                if(wts.get(i)>0) {
                    ArrayList<Intpair> dom=ch.get(i).getIntervalSetExp();
                    long coeff=wts.get(i);
                    // chop the smallest value. 
                    long smallestval=dom.get(0).lower;
                    
                    for(int j=0; j<dom.size(); j++) {
                        for(long k=dom.get(j).lower; k<=dom.get(j).upper; k++) {
                            if(k!=smallestval) {
                                coeffs_onevar.add( NumberConstant.make((coeff*k)-(coeff*smallestval)));
                                if(ch.get(i).isRelation() && k==1) {
                                    bools_onevar.add(ch.get(i));   /// Simplify the expression for boolean variables. 
                                }
                                else {
                                    bools_onevar.add(new Equals(ch.get(i), NumberConstant.make(k)));
                                }
                            }
                        }
                    }
                    
                    //  Adjust the other side of the binop to subtract the smallest val. 
                    cmp -= smallestval*coeff;
                }
                else {
                    // Should be boolean if there is a negative coeff. 
                    Intpair bnds=ch.get(i).getBounds();
                    assert bnds.lower>=0 && bnds.upper<=1;
                    
                    long coeff=wts.get(i);
                    cmp+=(-coeff);
                    
                    coeffs_onevar.add(NumberConstant.make(-coeff));
                    if(ch.get(i).isRelation()) {
                        bools_onevar.add(new Negate(ch.get(i)));
                    }
                    else {
                        bools_onevar.add(new Equals(ch.get(i), NumberConstant.make(0)));
                    }
                }
                
                amoproducts.add(CompoundMatrix.make(CompoundMatrix.make(coeffs_onevar), CompoundMatrix.make(bools_onevar)));
            }
        }
        
        AMOPB amo=new AMOPB(CompoundMatrix.make(amoproducts), NumberConstant.make(cmp), NumberConstant.make(encoding), new BooleanConstant(equality), allBool);
        
        ASTNode cts=amo.collectAMOGroups(m);
        
        return new NodeReplacement(amo, null, cts);
    }
    
    //////////////////////////////////////////////////////////////////////////
    //  Utility methods for transforming PB/LI constraints. 
    
    //  Returns 0 for not candidate, 1 for PB and 2 for LI. 
    public static int isPBLICandidate(ASTNode curnode) {
        //  Avoid non-top-level cts, which will fall back to the tree encoding. 
        if(curnode.getParent()!=null && !curnode.getParent().inTopAnd()) {
            return 0;
        }
        
        ArrayList<ASTNode> ch=null;
        
        //  Catch all cases of a sum in a binop.
        if(curnode instanceof ToVariable && curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant()) {
            ch=curnode.getChild(0).getChildren();
        }
        
        if(curnode instanceof Less && curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant()) {
            ch=curnode.getChild(0).getChildren();
        }
        
        if(curnode instanceof LessEqual && curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant()) {
            ch=curnode.getChild(0).getChildren();
        }
        
        if(curnode instanceof Less && curnode.getChild(1) instanceof WeightedSum && curnode.getChild(0).isConstant()) {
            // k < sum  becomes  -sum < -k  becomes  -sum <= -k-1
            ch=curnode.getChild(1).getChildren();
        }
        
        if(curnode instanceof LessEqual && curnode.getChild(1) instanceof WeightedSum && curnode.getChild(0).isConstant()) {
            // k <= sum  becomes  -sum <= -k 
            ch=curnode.getChild(1).getChildren();
        }
        
        if(ch==null) {
            return 0;
        }
        
        //  Is it entirely boolean
        boolean allBool=true;
        for(int i=0; i<ch.size(); i++) {
            if(!ch.get(i).isRelation()) {
                allBool=false;
                break;
            }
        }
        
        return allBool?1:2;
    }
    
    public static boolean isEquality(ASTNode curnode) {
        //  Assuming isCandidate returns non-zero value, is it an equality?
        
        return curnode instanceof ToVariable;
    }
    
    public static ASTNode extractAMOPB(Model _m, ASTNode curnode, boolean useEquality) {
        TransformSumToAMOPB tsa=new TransformSumToAMOPB(_m);
        
        NodeReplacement nr=tsa.processNode(curnode, useEquality, true);
        
        return nr.current_node;
    }
    
    //  Produces the tree encoding -- changes curnode in-place and also returns
    //  a NodeReplacement object. 
    public static NodeReplacement produceAMOPBTree(Model _m, ASTNode curnode) {
        //   To be used for tree encoding only. 
        TransformBreakupSum2 tb=new TransformBreakupSum2(_m);
        
        if(curnode.getChild(0) instanceof WeightedSum) {
            NodeReplacement nr=tb.processNode(curnode.getChild(0));
            curnode.setChild(0, nr.current_node);
            nr.current_node=curnode;  //  Leave new constraints in nr.
            return nr;
        }
        
        if(curnode.getChild(1) instanceof WeightedSum) {
            NodeReplacement nr=tb.processNode(curnode.getChild(1));
            curnode.setChild(1, nr.current_node);
            nr.current_node=curnode;  //  Leave new constraints in nr.
            return nr;
        }
        
        assert false : "Not a sum constraint in produceAMOPBTree";
        return null;
    }
    
    public static NodeReplacement produceAMOPB(Model _m, ASTNode curnode) {
        //   Do not use with tree -- does not set encoding. 
        //   Returns either a single AMOPB or an And of two (plus any new AMO constraints) 
        
        TransformSumToAMOPB tsa=new TransformSumToAMOPB(_m);
        
        return tsa.processNode(curnode, false, true);
    }
}

