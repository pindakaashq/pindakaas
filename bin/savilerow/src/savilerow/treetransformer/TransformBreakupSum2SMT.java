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
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.PriorityQueue;

import savilerow.CmdFlags;
import savilerow.expression.*;
import savilerow.model.*;

//  Break up a weighted sum -- this version takes the pair with the smallest set of values
//  and replaces with an aux.

public class TransformBreakupSum2SMT extends TreeTransformerBottomUp
{
    public TransformBreakupSum2SMT(Model _m) { super(_m); }

    protected NodeReplacement processNode(ASTNode curnode)
	{
	    // Sort for smallest domain first.
        class cmpastnode implements Comparator<ASTNode> {
            public int compare(ASTNode x, ASTNode y) {
                long size1= Intpair.numValues(x.getIntervalSetExp());
                long size2=Intpair.numValues(y.getIntervalSetExp());
                if(size1<size2) {
                    return -1;
                }
                else if(size1==size2) {
                    //  Domains are of equal size -- tie-break using the range.
                    Intpair p1=x.getBounds();
                    long range_1=p1.upper-p1.lower+1;

                    Intpair p2=y.getBounds();
                    long range_2=p2.upper-p2.lower+1;

                    if(range_1<range_2) {
                        return -1;
                    }
                    else if(range_1==range_2) {
                        return 0;
                    }
                    else {
                        return 1;
                    }
                }
                else {
                    return 1;
                }
            }
        }

	    if(curnode instanceof WeightedSum && curnode.numChildren()>3) {
            if(Sat.eligibleAMO(curnode)) {
                return null;
            }

            cmpastnode cmpast=new cmpastnode();

            PriorityQueue<ASTNode> p=new PriorityQueue<ASTNode>(curnode.numChildren(), cmpast);

            ArrayList<Long> wts=((WeightedSum)curnode).getWeights();

            for(int i=0; i<curnode.numChildren(); i++) {
                p.offer(new MultiplyMapper(curnode.getChild(i), NumberConstant.make(wts.get(i))));
            }

            ArrayList<ASTNode> newcts = new ArrayList<ASTNode>();

            // Bounds on intermediate aux variables -- if we have a top-level constraint x+y+z < 5, each intermediate aux variable can be <5 as well as the final aux var, as long as x,y,z are all non-negative.
            long lb=Long.MIN_VALUE;
            long ub=Long.MAX_VALUE;

            boolean allPos=true;
            boolean allNeg=true;
            for(int i=0; i<curnode.numChildren(); i++) {
                Intpair bnds=curnode.getChild(i).getBounds();
                if(bnds.lower<0) {
                    if(wts.get(i)>0) {
                        allPos=false;
                    }
                    else {
                        allNeg=false;
                    }
                }
                if(bnds.upper>0) {
                    if(wts.get(i)>0) {
                        allNeg=false;
                    }
                    else {
                        allPos=false;
                    }
                }
            }
            ASTNode par=curnode.getParent();
            if( (allNeg || allPos) && par.getParent().inTopAnd()) {
                if(par instanceof Less) {
                    if(curnode.getChildNo()==0 && allPos) {
                        ub=par.getChild(1).getBounds().upper-1;   // Bounded above by the rhs
                    }
                    if(curnode.getChildNo()==1 && allNeg) {
                        lb=par.getChild(0).getBounds().lower+1;   // Bounded below by the lhs.
                    }
                }
                if(par instanceof LessEqual) {
                    if(curnode.getChildNo()==0 && allPos) {
                        ub=par.getChild(1).getBounds().upper;   // Bounded above by the rhs.
                    }
                    if(curnode.getChildNo()==1 && allNeg) {
                        lb=par.getChild(0).getBounds().lower;   // Bounded below by the lhs.
                    }
                }
                if(par instanceof Equals || par instanceof ToVariable) {
                    if(curnode.getChildNo()==0) {
                        if(allPos) {
                            ub=par.getChild(1).getBounds().upper;
                        }
                        else if(allNeg) {
                            lb=par.getChild(1).getBounds().lower;
                        }
                    }
                    else {
                        // curnode is par.getChild(1)
                        if(allPos) {
                            ub=par.getChild(0).getBounds().upper;
                        }
                        else if(allNeg) {
                            lb=par.getChild(0).getBounds().lower;
                        }
                    }
                }
            }
            ASTNode maxdomain=new IntegerDomain(new Range(NumberConstant.make(lb), NumberConstant.make(ub)));

            // Do the tree decomposition.

            while(p.size()>3) {
                ASTNode m1=p.poll();
                ASTNode m2=p.poll();

                // Pull apart the MultiplyMappers and make a sum.
                ArrayList<Long> newwts=new ArrayList<Long>();
                newwts.add(m1.getChild(1).getValue());
                newwts.add(m2.getChild(1).getValue());
                ArrayList<ASTNode> ch=new ArrayList<ASTNode>();
                ch.add(m1.getChild(0));
                ch.add(m2.getChild(0));

                ASTNode newsumct=new WeightedSum(ch, newwts);

                ASTNode auxvar=m.global_symbols.newAuxHelper(newsumct, tightDomain(newsumct, maxdomain.copy()));

                ASTNode flatcon;
                if(CmdFlags.getAuxNonFunctional() && (par instanceof Less || par instanceof LessEqual) && par.getParent().inTopAnd()) {
                    if(curnode.getChildNo()==0) {
                        flatcon=new LessEqual(newsumct, auxvar);
                    }
                    else {
                        flatcon=new LessEqual(auxvar, newsumct);
                    }
                }
                else {
                    flatcon=new ToVariable(newsumct, auxvar);
                }

                m.global_symbols.auxVarRepresentsConstraint(auxvar.toString(), newsumct.toString());

                newcts.add(flatcon);
                p.offer(new MultiplyMapper(auxvar, NumberConstant.make(1)));
            }

            // Construct the replacement sum with at most 3 terms.
            ArrayList<ASTNode> repsumch=new ArrayList<ASTNode>();
            ArrayList<Long> repsumwts=new ArrayList<Long>();
            while(p.size()>0) {
                ASTNode mm=p.poll();
                repsumch.add(mm.getChild(0));
                repsumwts.add(mm.getChild(1).getValue());
            }

            return new NodeReplacement(new WeightedSum(repsumch, repsumwts), null, new And(newcts));
        }

        return null;
    }


    //  Copy and pasted from TransformMakeTable
    public ArrayList<ASTNode> getVariables(ASTNode exp) {
        HashSet<ASTNode> tmp=new HashSet<ASTNode>();
        getVariablesInner(exp, tmp);
        return new ArrayList<ASTNode>(tmp);
    }

    private void getVariablesInner(ASTNode exp, HashSet<ASTNode> varset) {
        if(exp instanceof Identifier && exp.getCategory()>ASTNode.Constant) {
            // Collect all identifiers except those that refer to a constant matrix.
            varset.add(exp);
        }
        else {
            for(int i=0; i<exp.numChildren(); i++) {
                getVariablesInner(exp.getChild(i), varset);
            }
        }
    }

    //  Create tight domain for aux var.
    //  Should really be in newAuxHelper somehow.
    public ASTNode tightDomain(ASTNode exp, ASTNode maxdomain) {
        ArrayList<ASTNode> vars=getVariables(exp);

        HashSet<Long> reachableVals=new HashSet<Long>();
        tightDomainRecurse(exp, vars, 0, reachableVals);

        ArrayList<Intpair> tmp=new ArrayList<Intpair>();
        for(Long i : reachableVals) {
            tmp.add(new Intpair(i,i));
        }
        Collections.sort(tmp);

        TransformSimplify ts=new TransformSimplify();
        ASTNode tdom=ts.transform(new Intersect(Intpair.makeDomain(tmp, false), maxdomain));

        return tdom;
    }

    private void tightDomainRecurse(ASTNode exp, ArrayList<ASTNode> vars, int i, HashSet<Long> vals) {
        TransformSimplify ts=new TransformSimplify();
        if(i==vars.size()) {
            ASTNode value=ts.transform(exp.copy());
            assert value.isConstant();
            vals.add(value.getValue());
        }
        else {
            ASTNode var=vars.get(i);
            ArrayList<Intpair> vardom=ts.transform( ((Identifier)var).getDomain().copy() ).getIntervalSet();

            for(int j=0; j<vardom.size(); j++) {
                for(long val=vardom.get(j).lower; val<=vardom.get(j).upper; val++) {
                    ReplaceASTNode r=new ReplaceASTNode(var, NumberConstant.make(val));
                    ASTNode innerexp=r.transform(exp.copy());
                    tightDomainRecurse(innerexp, vars, i+1, vals);
                }
            }
        }
    }
}