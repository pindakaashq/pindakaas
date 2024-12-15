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

//   Remove all PB constraints. 

public class TransformPBToNil extends TreeTransformerBottomUp
{
    public TransformPBToNil(Model _m) { super(_m); }
    
    protected NodeReplacement processNode(ASTNode curnode)
    {
        ArrayList<ASTNode> ch=null;
        ArrayList<Long> wts=null;
        long cmp=0;
        
        //  Catch all cases of a sum in a binop.
        if(curnode instanceof ToVariable && curnode.getChild(0) instanceof WeightedSum && curnode.getChild(1).isConstant()) {
            ch=curnode.getChild(0).getChildren();
            wts=((WeightedSum)curnode.getChild(0)).getWeights();
            
            cmp=curnode.getChild(1).getValue();
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
        
        if(ch!=null) {
            //  Is it entirely boolean
            boolean allBool=true;
            for(int i=0; i<ch.size(); i++) {
                if(!ch.get(i).isRelation()) {
                    allBool=false;
                    break;
                }
            }
            
            //  Check command-line flags.
            if((allBool && CmdFlags.getSatPBEnc()==SumEnc.TREE)
                || (!allBool && CmdFlags.getSatSumEnc()==SumEnc.TREE)) {
                return null;
            }
            
            // Up to here, identical to the TransformSumToAMOPB pass. 
            
            // Just remove the constraint that will become an MDD. 
            return new NodeReplacement(new BooleanConstant(true));
        }
        
	    return null;
    }
}

