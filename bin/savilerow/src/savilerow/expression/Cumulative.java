package savilerow.expression;
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

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.ArrayList;

import savilerow.CmdFlags;
import savilerow.model.SymbolTable;
import savilerow.treetransformer.TransformDecomposeCumulative;

// Renewable resource constraint.
// First argument is array of start time variables
// Second argument is durations of each task (constant)
// Third argument is the resource requirements of each task (constant)
// Fourth argument is the resource consumption limit at all time steps (constant)
// All may be decision vars/expressions. 

public class Cumulative extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public Cumulative(ASTNode start, ASTNode dur, ASTNode res, ASTNode limit) {
        super(start, dur, res, limit);
    }
    
    public ASTNode copy() {
        return new Cumulative(getChild(0), getChild(1), getChild(2), getChild(3));
    }
    
    public boolean isRelation() {
        return true;
    }
    
    public boolean typecheck(SymbolTable st) {
        for(int i=0; i<4; i++) {
            if(!getChild(i).typecheck(st)) {
                return false;
            }
        }
        if (getChild(0).getDimension() != 1) {
            CmdFlags.println("ERROR: Expected one-dimensional matrix in first argument of cumulative: " + this);
            return false;
        }
        if (getChild(1).getDimension() != 1) {
            CmdFlags.println("ERROR: Expected one-dimensional matrix in second argument of cumulative: " + this);
            return false;
        }
        if (getChild(2).getDimension() != 1) {
            CmdFlags.println("ERROR: Expected one-dimensional matrix in third argument of cumulative: " + this);
            return false;
        }
        if(getChild(3).getDimension()!=0) {
            CmdFlags.println("ERROR: Expected scalar in fourth argument of cumulative: " + this);
            return false;
        }
        
        return true;
    }
    
    public ASTNode simplify() {
        ASTNode starts = getChildConst(0);
        ASTNode durations = getChildConst(1);
        ASTNode resourceReqs = getChildConst(2);
        ASTNode bound = getChild(3);
        
        if (!(starts instanceof CompoundMatrix)) {
            if (starts instanceof EmptyMatrix) {
                return new LessEqual(NumberConstant.make(0), bound);
            }
            else {
                return null; // argument is not yet a matrix literal. 
            }
        }
        
        if (starts.getCategory() == ASTNode.Constant && durations.getCategory() == ASTNode.Constant) {
            // Replace with task decomposition since start times and durations are fixed. 
            // As each task starts, the set of other tasks running is known so the resource constraint
            // is a simple linear inequality. 
            return TransformDecomposeCumulative.taskDecomp(starts, durations, resourceReqs, bound);
        }
        
        if(bound.getBounds().upper < 0) {
            return new BooleanConstant(false);
        }
        
        return null;
    }
    
    //  Direct to OR-Tools
    /*@Override
    public CumulativeConstraint toConstraint(CpModel m, HashMap<String, IntVar> vars) {
        ASTNode starts = getChildConst(0);
        ASTNode durations = getChildConst(1);
        ASTNode resourceReqs = getChildConst(2);

        CumulativeConstraint cc = m.addCumulative(getChild(3).toLinearArgument(m, vars));
        for (int i = 1; i < starts.numChildren(); i++) {
            ASTNode start = starts.getChild(i);
            ASTNode duration = durations.getChild(i);
            String name = "end_unused" + hashCode() + i;
            Intpair bounds = (new WeightedSum(start, duration)).getBounds();
            IntVar end_unused = m.newIntVar(bounds.lower, bounds.upper, name);
            IntervalVar v = m.newIntervalVar(
                start.toLinearArgument(m, vars), 
                duration.toLinearArgument(m, vars),
                end_unused,
                "interval("  + starts.toString() + duration.toString() + ")"
            );
            cc.addDemand(v, resourceReqs.getChild(i).toLinearArgument(m, vars));
        }
        return cc;
    }*/
    
    public ASTNode normalise() {
        // sort by hashcode
        if(!(getChild(0) instanceof CompoundMatrix && getChild(1) instanceof CompoundMatrix && getChild(2) instanceof CompoundMatrix)) {
            return this;
        }
        
        ArrayList<ASTNode> ch=new ArrayList<>();
        for(int i=1; i<getChild(0).numChildren(); i++) {
            ch.add(new Container(getChild(0).getChild(i), getChild(1).getChild(i), getChild(2).getChild(i)));
        }
        
        boolean changed = sortByHashcode(ch);
        if (changed) {
            //  Unpack
            ArrayList<ASTNode> x=new ArrayList<>();
            ArrayList<ASTNode> dur=new ArrayList<>();
            ArrayList<ASTNode> res=new ArrayList<>();
            
            for(int i=0; i<ch.size(); i++) {
                x.add(ch.get(i).getChild(0));
                dur.add(ch.get(i).getChild(1));
                res.add(ch.get(i).getChild(2));
            }
            
            return new Cumulative(CompoundMatrix.make(x), CompoundMatrix.make(dur), CompoundMatrix.make(res), getChild(3));
        } else {
            return this;
        }
    }
    
    public ASTNode normaliseAlpha() {
        // sort alphabetically
        if(!(getChild(0) instanceof CompoundMatrix && getChild(1) instanceof CompoundMatrix && getChild(2) instanceof CompoundMatrix)) {
            return null;
        }
        
        ArrayList<ASTNode> ch=new ArrayList<>();
        for(int i=1; i<getChild(0).numChildren(); i++) {
            ch.add(new Container(getChild(0).getChild(i), getChild(1).getChild(i), getChild(2).getChild(i)));
        }
        
        boolean changed = sortByAlpha(ch);
        if (changed) {
            //  Unpack
            ArrayList<ASTNode> x=new ArrayList<>();
            ArrayList<ASTNode> dur=new ArrayList<>();
            ArrayList<ASTNode> res=new ArrayList<>();
            
            for(int i=0; i<ch.size(); i++) {
                x.add(ch.get(i).getChild(0));
                dur.add(ch.get(i).getChild(1));
                res.add(ch.get(i).getChild(2));
            }
            
            return new Cumulative(CompoundMatrix.make(x), CompoundMatrix.make(dur), CompoundMatrix.make(res), getChild(3));
        } else {
            return null;
        }
    }
    
    @Override 
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        if(CmdFlags.getChuffedtrans()) {
            b.append("constraint chuffed_cumulative(");
        }
        else if(CmdFlags.getGecodetrans()) {
            b.append("constraint cumulatives(");
        }
        else {
            b.append("constraint fzn_cumulative(");
        }
        getChild(0).toFlatzinc(b, false);
        b.append(",");
        getChild(1).toFlatzinc(b, false);
        b.append(",");
        getChild(2).toFlatzinc(b, false);
        b.append(",");
        getChild(3).toFlatzinc(b, false);
        b.append(");");
    }

    @Override
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("cumulative(");
        getChild(0).toMinizinc(b, false);
        b.append(",");
        getChild(1).toMinizinc(b, false);
        b.append(",");
        getChild(2).toMinizinc(b, false);
        b.append(",");
        getChild(3).toMinizinc(b, false);
        b.append(");");
    }
    
    public String toString() {
        return generic_to_string("cumulative");
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //  JSON output for symmetry detection
    
    //  Todo
    /*
    public void toJSON(StringBuilder bf) {
        toJSONHeader(bf, true);
        // children
        bf.append("\"Children\": [");
        if(getChild(0) instanceof CompoundMatrix && getChild(0).numChildren()==3) {
            //   Special case for binary != constraint.
            getChild(0).getChild(1).toJSON(bf);
            bf.append(", ");
            getChild(0).getChild(2).toJSON(bf);
        }
        else {
            // Same as toJSON method in ASTNode.
            for (int i = 0; i < numChildren(); i++) {
                bf.append("\n");
                getChild(i).toJSON(bf);
                // not last child
                if (i < numChildren() - 1) {
                    bf.append(",");
                }
            }
        }
        bf.append("]\n}");
    }
    
    public boolean childrenAreSymmetric() {
        return (getChild(0) instanceof CompoundMatrix && getChild(0).numChildren()==3);
    }
    
    public boolean isChildSymmetric(int childIndex) {
        // If not a binary != ct, then the matrix inside should be regarded as symmetric.
        return !(getChild(0) instanceof CompoundMatrix && getChild(0).numChildren()==3);
    }

    public boolean canChildBeConvertedToDifference(int childIndex) {
        return isMyOnlyOtherSiblingEqualZero(childIndex);
    }
    */
}
