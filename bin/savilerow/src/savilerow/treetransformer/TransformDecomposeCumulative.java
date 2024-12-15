package savilerow.treetransformer;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Peter Nightingale and Luke Ryan
    
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
import savilerow.expression.*;

public class TransformDecomposeCumulative extends TreeTransformerBottomUpNoWrapper
{
    private boolean propagate;
    
    public TransformDecomposeCumulative(boolean _propagate) { 
        super(null);
        propagate = _propagate;
    }
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
        if(curnode instanceof Cumulative) {
            boolean backendHasCumul=(CmdFlags.getOrtoolstrans() || CmdFlags.getGecodetrans() || CmdFlags.getChuffedtrans() || CmdFlags.getMinizinctrans()) && !propagate;
            
            if(!backendHasCumul || !curnode.getParent().inTopAnd()) {
                return new NodeReplacement(decomp(curnode));
            }
            
            //  Chuffed doesn't allow variable durations, resources, or bound.
            if(CmdFlags.getChuffedtrans() && (curnode.getChild(1).getCategory()>ASTNode.Constant || curnode.getChild(2).getCategory()>ASTNode.Constant || curnode.getChild(3).getCategory()>ASTNode.Constant)) {
                return new NodeReplacement(decomp(curnode));
            }
        }
        return null;
    }
    
    private static ASTNode decomp(ASTNode curnode) {
        ASTNode starts = curnode.getChildConst(0);
        ASTNode durations = curnode.getChildConst(1);
        ASTNode resourceReqs = curnode.getChildConst(2);
        ASTNode bound = curnode.getChild(3);
        
        assert starts instanceof CompoundMatrix;
        assert durations instanceof CompoundMatrix;
        assert resourceReqs instanceof CompoundMatrix;
        
        Intpair p=starts.getChild(1).getBounds();
        Intpair dur=durations.getChild(1).getBounds();
        
        long start=p.lower;
        long end=p.upper+dur.upper;
        
        for(int i=2; i<starts.numChildren(); i++) {
            p=starts.getChild(i).getBounds();
            dur=durations.getChild(i).getBounds();
            if(start>p.lower) {
                start=p.lower;
            }
            if(end<p.upper+dur.upper) {
                end=p.upper+dur.upper;
            }
        }
        
        if(end-start+1 > 1000) {
            return taskDecomp(starts, durations, resourceReqs, bound);
        }
        else {
            return timeDecomp(starts, durations, resourceReqs, bound, start, end);
        }
    }
    
    private static ASTNode timeDecomp(ASTNode starts, ASTNode durations, ASTNode resourceReqs, ASTNode bound, long start, long end) {
        ArrayList<ASTNode> ct=new ArrayList<>();
        
        ASTNode zero = NumberConstant.make(0);
        
        ct.add(new LessEqual(zero, bound));
        
        for (int i = 1; i < starts.numChildren(); i++) {
            ct.add(new LessEqual(zero, durations.getChild(i)));
            ct.add(new LessEqual(zero, resourceReqs.getChild(i)));
        }
        
        for(long timestep=start; timestep<=end; timestep++) {
            ArrayList<ASTNode> sum = new ArrayList<>();
            for(int i=1; i<starts.numChildren(); i++) {
                sum.add(new Times(resourceReqs.getChild(i), 
                    new And(new LessEqual(starts.getChild(i), NumberConstant.make(timestep)), 
                        new Less(NumberConstant.make(timestep), new WeightedSum(starts.getChild(i), durations.getChild(i))))));
            }
            ct.add(new LessEqual(new WeightedSum(sum), bound));
        }
        
        return new And(ct);
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Task decomposition
    
    public static ASTNode taskDecomp(ASTNode starts, ASTNode durations, ASTNode resourceReqs, ASTNode bound) {
        ArrayList<ASTNode> ct=new ArrayList<>();
        
        ASTNode zero = NumberConstant.make(0);
        
        ct.add(new LessEqual(zero, bound));
        
        for (int i = 1; i < starts.numChildren(); i++) {
            ct.add(new LessEqual(zero, durations.getChild(i)));
            ct.add(new LessEqual(zero, resourceReqs.getChild(i)));
            
            ASTNode usage = usage(i, starts, durations, resourceReqs);
            ct.add(new LessEqual(usage, bound));
        }
        
        return new And(ct);
    }
    
    //  Part of task decomposition -- resource usage at the start time of task i. 
    private static ASTNode usage(int i, ASTNode starts, ASTNode durations, ASTNode resourceReqs) {
        ArrayList<ASTNode> sumTerms = new ArrayList<>();
        
        for (int j = 1; j < starts.numChildren(); j++) {
            sumTerms.add(
                new Times(
                    new And(
                        new LessEqual(starts.getChild(j), starts.getChild(i)),
                        new Less(starts.getChild(i), new WeightedSum(starts.getChild(j), durations.getChild(j)))
                    ),
                    resourceReqs.getChild(j)
                )
            );
        }
        
        return new WeightedSum(sumTerms);
    }
    
}
