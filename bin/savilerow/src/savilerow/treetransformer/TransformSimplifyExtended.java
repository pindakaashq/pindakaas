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

import savilerow.CmdFlags;
import savilerow.expression.*;
import savilerow.model.Model;

//  A unique one, call the simplify method on curnode -- implements lots of small rules.
//  Must be bottom up so that each node can call methods on its children knowing they
//  are well formed. e.g. not Tag. 

// This version also includes deleting variables. Rewrites the symbol table;
// must not be used on constraints that are not in the model. 

public class TransformSimplifyExtended extends TreeTransformerBottomUpNoWrapper
{
    public TransformSimplifyExtended(Model m) { super(m);}
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    // tree nodes are supposed to be immutable (apart from their child pointers), so if it has changed
	    // then it should be a new node.
	    ASTNode tmp=curnode.simplify();
	    if(tmp!=null) {
	        assert tmp!=curnode;   ///   simplify not allowed to return 'this'
	        return new NodeReplacement(tmp);
	    }
	    
	    if(CmdFlags.getUseDeleteVars()) {
	        return doDeleteVars(curnode);
	    }
	    
	    return null;
    }
    
    private NodeReplacement doDeleteVars(ASTNode curnode) {
        //  Top level expressions only (not expressions nested in an And inside the top level And).
        // This is to guarantee the top level And is replaced and all its children traversed again.
        if(curnode.getParent()!=null 
            && ( (curnode.getParent() instanceof And && curnode.getParent().getParent() instanceof Top)
                || curnode.getParent() instanceof Top)) {
            // Only do assignment after aggregation has finished because it prevents aggregation of allDiff. 
            boolean doAssignVar=(!CmdFlags.getUseAggregate()) || CmdFlags.getAfterAggregate();
	        // Equality types.
	        if(curnode instanceof Equals || curnode instanceof Iff || curnode instanceof ToVariable) {
	            ASTNode c0=curnode.getChild(0);
	            ASTNode c1=curnode.getChild(1);
	            if(c0 instanceof Identifier && c1.isConstant() && doAssignVar && !m.global_symbols.preserveVariable(c0)) {
	                //  Makes a big assumption: that the equality would already have simplified to false 
	                //  if the value is not in domain. 
	                m.global_symbols.assignVariable(c0, c1);
                    return new NodeReplacement(new BooleanConstant(true));
                }
                if(c1 instanceof Identifier && c0.isConstant() && doAssignVar && !m.global_symbols.preserveVariable(c1)) {
                    //  Makes a big assumption: that the equality would already have simplified to false 
	                //  if the value is not in domain.
                    m.global_symbols.assignVariable(c1, c0);
                    return new NodeReplacement(new BooleanConstant(true));
                }
	            if(c0 instanceof Identifier && c1 instanceof Identifier
	                && !(c0.equals(c1))
	                && (!m.global_symbols.preserveVariable(c0) || !m.global_symbols.preserveVariable(c1)) ) {
	                // Second condition makes sure the two identifiers are not the same. This can occur 
	                // when there is a loop of equalities.
	                m.global_symbols.unifyVariables(c0, c1);
	                return new NodeReplacement(new BooleanConstant(true));
	            }
	            
	            // Special case for SAT where one variable is a linear mapping of another.
	            // Does not work for unknown reason. 
	            if(false && CmdFlags.getSattrans() && !CmdFlags.getSMTtrans()) {
	                if(c0 instanceof Identifier && isLinearMapping(c1, true) && (!c1.contains(c0)) && !m.global_symbols.preserveVariable(c0)) {
	                    ASTNode replct=new InSet(c1, Intpair.makeDomain(c0.getIntervalSetExp(), c0.isRelation()));
	                    m.global_symbols.unifyVariablesLinear(c0, c1);
	                    return new NodeReplacement(replct);
	                }
	                if(c1 instanceof Identifier && isLinearMapping(c0, true) && (!c0.contains(c1)) && !m.global_symbols.preserveVariable(c1)) {
	                    ASTNode replct=new InSet(c0, Intpair.makeDomain(c1.getIntervalSetExp(), c1.isRelation()));
	                    m.global_symbols.unifyVariablesLinear(c1, c0);
	                    return new NodeReplacement(replct);
	                }
	            }
	            
	            // Cases where one variable is the negation of the other
	            if(CmdFlags.getMiniontrans() || CmdFlags.getSattrans()) {
	                if(c0.isRelation() && c1.isRelation()) {  //  Both boolean.
                        if(c0 instanceof Identifier && c1 instanceof Negate && c1.getChild(0) instanceof Identifier
                            && (!m.global_symbols.preserveVariable(c0) || !m.global_symbols.preserveVariable(c1.getChild(0)))) {
                            m.global_symbols.unifyVariablesNegated(c0, c1);
                            return new NodeReplacement(new BooleanConstant(true));
                        }
                        if(c1 instanceof Identifier && c0 instanceof Negate && c0.getChild(0) instanceof Identifier
                            && (!m.global_symbols.preserveVariable(c0.getChild(0)) || !m.global_symbols.preserveVariable(c1))) {
                            m.global_symbols.unifyVariablesNegated(c1, c0);
                            return new NodeReplacement(new BooleanConstant(true));
                        }
                    }
                }
            }
            
            // Bare or negated boolean variable in the top-level And.
            if(curnode instanceof Identifier && doAssignVar && !m.global_symbols.preserveVariable(curnode)) {
                m.global_symbols.assignVariable(curnode, new BooleanConstant(true));
                return new NodeReplacement(new BooleanConstant(true));
            }
            if(curnode instanceof Negate && curnode.getChild(0) instanceof Identifier && doAssignVar && !m.global_symbols.preserveVariable(curnode.getChild(0))) {
                m.global_symbols.assignVariable(curnode.getChild(0), new BooleanConstant(false));
                return new NodeReplacement(new BooleanConstant(true));
            }
            
            //  Put unary constraints into the domain. 
            if(curnode instanceof InSet && curnode.getChild(0) instanceof Identifier 
                && curnode.getChild(0).getCategory()==ASTNode.Decision
                && curnode.getChild(1).getCategory()==ASTNode.Constant) {
                String n=curnode.getChild(0).toString();
                ASTNode newdom=new Intersect(m.global_symbols.getDomain(n), curnode.getChild(1));
                TransformSimplify ts=new TransformSimplify();
                m.global_symbols.setDomain(n, ts.transform(newdom));
                return new NodeReplacement(new BooleanConstant(true));
            }
            
            //  Constants in AllDiff.   These appear in definedness cts which may be(come) top-level constraints.
            if(curnode instanceof AllDifferent) {
                ArrayList<Intpair> consts=new ArrayList<Intpair>();
                for(int i=1; i<curnode.getChild(0).numChildren(); i++) {
                    if(curnode.getChild(0).getChild(i).isConstant()) {
                        long v=curnode.getChild(0).getChild(i).getValue();
                        consts.add(new Intpair(v, v));
                    }
                }
                
                if(consts.size()>0) {
                    Intpair.normalise(consts);
                    ArrayList<Intpair> remainingvals=Intpair.complement(consts);
                    
                    for(int i=1; i<curnode.getChild(0).numChildren(); i++) {
                        ASTNode c=curnode.getChild(0).getChild(i);
                        if(c instanceof Identifier && c.getCategory()==ASTNode.Decision) {
                            ArrayList<Intpair> domain=c.getIntervalSetExp();
                            if(domain!=null) {
                                ArrayList<Intpair> inter=Intpair.intersection(domain, remainingvals);
                                if(! inter.equals(domain)) {
                                    m.global_symbols.setDomain(c.toString(), Intpair.makeDomain(inter, c.isRelation()));
                                }
                            }
                        }
                    }
                }
            }
            
            // LessEqual and Less -- trim bounds.
            if(curnode instanceof LessEqual || curnode instanceof Less) {
                Intpair bnds1=curnode.getChild(0).getBounds();
                Intpair bnds2=curnode.getChild(1).getBounds();
                
                int adjust=(curnode instanceof Less)?-1:0;
                
                if(curnode.getChild(0) instanceof Identifier && curnode.getChild(0).getCategory()==ASTNode.Decision && bnds1.upper > bnds2.upper+adjust) {
                    // Trim child 0 upper bound.
                    setUB(curnode.getChild(0), bnds2.upper+adjust);
                }
                
                if(curnode.getChild(1) instanceof Identifier && curnode.getChild(1).getCategory()==ASTNode.Decision && bnds2.lower < bnds1.lower-adjust) {
                    //  Trim child 1 upper bound.
                    setLB(curnode.getChild(1), bnds1.lower-adjust);
                }
            }
            
            // Equality types -- trim bounds.
            if(curnode instanceof ToVariable || curnode instanceof Equals || curnode instanceof Iff) {
                Intpair bnds1=curnode.getChild(0).getBounds();
                Intpair bnds2=curnode.getChild(1).getBounds();
                
                if(curnode.getChild(0) instanceof Identifier && curnode.getChild(0).getCategory()==ASTNode.Decision) {
                    if(bnds1.upper > bnds2.upper) {
                        // Trim child 0 upper bound.
                        setUB(curnode.getChild(0), bnds2.upper);
                    }
                    if(bnds1.lower < bnds2.lower) {
                        // Trim child 0 lower bound.
                        setLB(curnode.getChild(0), bnds2.lower);
                    }
                }
                
                if(curnode.getChild(1) instanceof Identifier && curnode.getChild(1).getCategory()==ASTNode.Decision) {
                    if(bnds2.upper > bnds1.upper) {
                        // Trim child 1 upper bound.
                        setUB(curnode.getChild(1), bnds1.upper);
                    }
                    if(bnds2.lower < bnds1.lower) {
                        //  Trim child 1 lower bound.
                        setLB(curnode.getChild(1), bnds1.lower);
                    }
                }
            }
            
            //  MultiStage has an implicit unary constraint.
            if(curnode instanceof IncomparabilityFunction && curnode.getChild(0) instanceof Identifier && curnode.getChild(1).getCategory()==ASTNode.Constant) {
                ASTNode dom=((Identifier)curnode.getChild(0)).getDomain();
                if(dom.getCategory()==ASTNode.Constant) {
                    ArrayList<Intpair> listvals=new ArrayList<Intpair>();
                    
                    for(int i=1; i<curnode.getChild(1).numChildren(); i++) {
                        listvals=Intpair.union(listvals, curnode.getChild(1).getChild(i).getIntervalSetExp());
                    }
                    
                    ArrayList<Intpair> olddom=dom.getIntervalSet();
                    
                    ArrayList<Intpair> a=Intpair.intersection(olddom, listvals);
                    
                    if(! a.equals(olddom)) {
                        String n=curnode.getChild(0).toString();
                        m.global_symbols.setDomain(n, Intpair.makeDomain(a, curnode.getChild(0).isRelation()));
                    }
                }
            }
        }
        return null;
    }
    
    private boolean isLinearMapping(ASTNode a, boolean top) {
        if(a instanceof ShiftMapper || a instanceof MultiplyMapper) {
            return isLinearMapping(a.getChild(0), false);
        }
        else {
            return (a instanceof Identifier) && !top;
        }
    }
    
    private void setUB(ASTNode ch, long ub) {
        ArrayList<Intpair> trim=new ArrayList<Intpair>(1);
        trim.add(new Intpair(Long.MIN_VALUE, ub));
        ArrayList<Intpair> domain=ch.getIntervalSetExp();
        if(domain!=null) {
            m.global_symbols.setDomain(ch.toString(),
                Intpair.makeDomain( Intpair.intersection(domain, trim), ch.isRelation() ));
        }
    }
    
    private void setLB(ASTNode ch, long lb) {
        ArrayList<Intpair> trim=new ArrayList<Intpair>(1);
        trim.add(new Intpair(lb, Long.MAX_VALUE));
        ArrayList<Intpair> domain=ch.getIntervalSetExp();
        if(domain!=null) {
            m.global_symbols.setDomain(ch.toString(),
                Intpair.makeDomain( Intpair.intersection(domain, trim), ch.isRelation() ));
        }
    }
}

