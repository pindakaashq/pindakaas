package savilerow;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Patrick Spracklen and Peter Nightingale
    
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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import savilerow.expression.*;
import savilerow.model.*;
import savilerow.treetransformer.TransformMIPOutput;

public class MIP
{
    public MIP(Model _m) {
        m=_m;
        gs=_m.global_symbols;
    }
    
    Model m;
    SymbolTable gs;
    
    //  For each variable, is it retained in the MIP output (in varsint), and
    //  does it have a 0/1 representation (in vars01). 
    HashSet<String> vars01=new HashSet<String>();
    HashSet<String> varsint=new HashSet<String>();
    //  Will have one more type: set of intervals representation. 
    
    //  Mapping from integer values to 0/1 vars representing the value. 
    HashMap<String, HashMap<Long, String>> varTo01=new HashMap<>();
    
    public void process() {
        collect01();
        
        ArrayList<ASTNode> newcts=generate01Vars();
        
        newcts.addAll(generateDomainConstraints());
        
        m.constraints.setChild(0, new And(m.constraints.getChild(0), new And(newcts)));
        
        replace01();
    }
    
    
    //  Collect which variables need a 01 (or domain) representation and which need an integer representation. 
    public void collect01() {
        ArrayDeque<ASTNode> todo=new ArrayDeque<ASTNode>();
        todo.add(m.constraints.getChild(0));
        
        while(!todo.isEmpty()) {
            ASTNode curnode=todo.poll();
            
            if(curnode instanceof Identifier) {
                // For now, all variables marked for 'int' output
                varsint.add(curnode.toString());
                
                if(!curnode.isRelation()) {
                    Intpair b=curnode.getBounds();
                    
                    if(b.lower<0 || b.upper>1) {
                        //  Not a bool or 0/1 variable
                        ASTNode mapped=curnode;
                        // lift above mappers/matrices
                        while(mapped.getParent() instanceof MultiplyMapper || mapped.getParent() instanceof ShiftMapper || mapped.getParent() instanceof CompoundMatrix) {
                            mapped=mapped.getParent();
                        }
                        
                        ASTNode p=mapped.getParent();
                        
                        //  Check for types that require a 0/1 repn. 
                        if( ((p instanceof Equals || p instanceof LessEqual || p instanceof Less) && (p.getChild(0).isConstant() || p.getChild(1).isConstant()))    //  var binop const
                            || ( p instanceof AllDifferent && p.getChild(0).numChildren()==3 && (p.getChild(0).getChild(1).isConstant() || p.getChild(0).getChild(2).isConstant()) ) // Var not-equal a constant. 
                            || p instanceof InSet) {    //  not fine-grained enough. 
                            vars01.add(curnode.toString());
                        }
                    }
                }
            }
            
            todo.addAll(curnode.getChildren());
        }
    }
    
    
    
    //////////////////////////////////////////////////////////////////////////
    //  Generate the 0/1 variables when required. 
    
    public ArrayList<ASTNode> generate01Vars() {
        ArrayList<ASTNode> newcts=new ArrayList<>();
        
        categoryentry c = gs.category_first;
        
        while(c != null) {
            if(vars01.contains(c.name)) {
                HashMap<Long, String> map=new HashMap<Long, String>();
                
                varTo01.put(c.name, map);
                
                ArrayList<Intpair> intervals=gs.getDomain(c.name).getIntervalSet();
                
                // Also generate two constraints to link the 0/1 and integer variables.
                
                ArrayList<ASTNode> ctvars=new ArrayList<>();
                ArrayList<Long> ctweights=new ArrayList<>();
                
                ArrayList<ASTNode> ctvars2=new ArrayList<>();
                ArrayList<Long> ctweights2=new ArrayList<>();
                
                for(int i=0; i<intervals.size(); i++) {
                    for(long val=intervals.get(i).lower; val<=intervals.get(i).upper; val++) {
                        ASTNode aux=gs.newAuxiliaryVariable(0,1);
                        map.put(val, aux.toString());
                        
                        ctvars.add(aux);
                        ctweights.add(1L);
                        
                        ctvars2.add(aux);
                        ctweights2.add(val);
                    }
                }
                
                //  First constraint - 0/1 vars sum to 1. 
                newcts.add(new Equals(new WeightedSum(ctvars, ctweights), NumberConstant.make(1L)));
                
                // Second constraint -- link 0/1 to integer variable
                ctvars2.add(new Identifier(m, c.name));
                ctweights2.add(-1L);
                newcts.add(new Equals(new WeightedSum(ctvars2, ctweights2), NumberConstant.make(0L)));
            }
            
            c=c.next;
        }
        
        return newcts;
    }
    
    public ArrayList<ASTNode> generateDomainConstraints() {
        //  For each variable that is not 0/1 or bool, that has holes in the domain,
        //  output constraints to ensure it takes a value in domain. 
        ArrayList<ASTNode> newcts=new ArrayList<>();
        
        categoryentry c = gs.category_first;
        while (c != null) {
            if (c.cat == ASTNode.Decision || c.cat == ASTNode.Auxiliary) {
                ArrayList<Intpair> intervals=gs.getDomain(c.name).getIntervalSet();
                
                //  if 0/1 variables already exist, then no need for additional
                //  constraints. 
                
                if((!vars01.contains(c.name)) && intervals.size()>1) {
                    //  Introduce a new 0/1 variable for each interval. 
                    
                    ArrayList<ASTNode> ctvars=new ArrayList<>();
                    ArrayList<Long> ctcoeffs=new ArrayList<>();
                    
                    for(int i=0; i<intervals.size(); i++) {
                        ASTNode aux=gs.newAuxiliaryVariable(0,1);
                        ctvars.add(aux);
                        ctcoeffs.add(1L);
                    }
                    
                    //  New variables sum to 1. 
                    newcts.add(new Equals(new WeightedSum(ctvars, ctcoeffs), NumberConstant.make(1L)));
                    
                    for(int i=0; i<intervals.size(); i++) {
                        // aux var implies within interval.
                        if(i>0) {
                            newcts.add(implyIneq(ctvars.get(i), new Times(new Identifier(m, c.name), NumberConstant.make(-1)), -intervals.get(i).lower));
                        }
                        
                        if(i<intervals.size()-1) {
                            newcts.add(implyIneq(ctvars.get(i), new Identifier(m, c.name), intervals.get(i).upper));
                        }
                    }
                }
            }
            
            c = c.next;
        }
        return newcts;
    }
    
    //  Replace unary Boolean expressions that use an integer variable with their 0/1 equivalent. 
    public void replace01() {
        TransformMIPOutput tmo=new TransformMIPOutput(this);
        m.constraints=tmo.transform(m.constraints);
    }
    
    /////////////////////////////////////////////////////////////////////////
    //
    //   Utilities
    
    //  implement implication by big-M
    public ASTNode implyIneq(ASTNode r, ASTNode term, long k) {
        System.out.println("implyineq: "+r+", "+term+", "+k);
        
        Intpair p=term.getBounds();
        
        if(p.upper<=k) {
            return new BooleanConstant(true);
        }
        
        long M=p.upper-k;
        
        ArrayList<ASTNode> vars=new ArrayList<>();
        ArrayList<Long> coeffs=new ArrayList<>();
        
        vars.add(term);
        vars.add(r);
        coeffs.add(1L);
        coeffs.add(M);
        
        ASTNode ret = new LessEqual(new WeightedSum(vars, coeffs), NumberConstant.make(k+M));
        System.out.println(ret);
        return ret;
    }
    
    //  Disequality between two integers
    public ASTNode diseq(ASTNode a, ASTNode b) {
        // a+1 <= b case
        ArrayList<ASTNode> terms=new ArrayList<>();
        terms.add(a);
        terms.add(NumberConstant.make(1));
        terms.add(b);
        ArrayList<Long> coeffs=new ArrayList<>();
        coeffs.add(1L);
        coeffs.add(1L);
        coeffs.add(-1L);
        ASTNode lhs1=new WeightedSum(terms, coeffs);
        
        // b+1 <= a case
        terms.clear();
        terms.add(b);
        terms.add(NumberConstant.make(1));
        terms.add(a);
        ASTNode lhs2=new WeightedSum(terms, coeffs);
        
        return disjunction2(lhs1, 0, lhs2, 0);
    }
    
    //  Disequality between two integers if impl is true
    public ASTNode diseq(ASTNode a, ASTNode b, ASTNode impl) {
        ASTNode conj=diseq(a, b);
        
        // Make constraints in conj conditional on impl being true. 
        conj.setChild(0, implyIneq(impl, conj.getChild(0).getChild(0), conj.getChild(0).getChild(1).getValue()));
        conj.setChild(1, implyIneq(impl, conj.getChild(1).getChild(0), conj.getChild(1).getChild(1).getValue()));
        
        return conj;
    }
    
    //  Equality between two integers a and b if impl is true/1. 
    public ASTNode equal(ASTNode a, ASTNode b, ASTNode impl) {
        ArrayList<ASTNode> terms=new ArrayList<>();
        terms.add(a);
        terms.add(b);
        ArrayList<Long> coeffs=new ArrayList<>();
        coeffs.add(1L);
        coeffs.add(-1L);
        
        ASTNode e1=new WeightedSum(terms, coeffs);
        
        ASTNode c1=implyIneq(impl, e1, 0);
        
        coeffs.clear();
        coeffs.add(-1L);
        coeffs.add(1L);
        
        ASTNode e2=new WeightedSum(terms, coeffs);
        
        ASTNode c2=implyIneq(impl, e2, 0);
        return new And(c1, c2);
    }
    
    public ASTNode disjunction2(ASTNode lhs1, long k1, ASTNode lhs2, long k2) {
        //  Disjunction of two linear inequalities using 1 0/1 variable.
        ASTNode aux=gs.newAuxiliaryVariable(0,1);
        
        ArrayList<ASTNode> terms=new ArrayList<>();
        terms.add(aux);
        terms.add(NumberConstant.make(1));
        ArrayList<Long> coeffs=new ArrayList<>();
        coeffs.add(-1L);
        coeffs.add(1L);
        ASTNode notaux=new WeightedSum(terms, coeffs);
        
        ASTNode a1=implyIneq(aux, lhs1, k1);
        ASTNode a2=implyIneq(notaux, lhs2, k2);
        return new And(a1, a2);
    }
    
    //  Negate a 0/1
    public ASTNode negate(ASTNode a) {
        return new WeightedSum(new ASTNode[]{NumberConstant.make(1), a}, new long[]{1, -1});
    }
    
    public ASTNode inset(ASTNode constraint, ASTNode a, ArrayList<Intpair> intervals) {
        ArrayList<ASTNode> auxs=new ArrayList<ASTNode>();
        for(int i=0; i<intervals.size(); i++) {
            for(long val=intervals.get(i).lower; val<=intervals.get(i).upper; val++) {
                auxs.add(get01var(a, val));
            }
        }
        
        if(constraint.getParent().inTopAnd()) {
            //  Top-level constraint.
            return new LessEqual(NumberConstant.make(1), new WeightedSum(auxs));
        }
        else {
            return new WeightedSum(auxs);
        }
    }
    
    public ASTNode stripMappers(ASTNode a) {
        while(a instanceof MultiplyMapper || a instanceof ShiftMapper) {
            a=a.getChild(0);
        }
        return a;
    }
    
    //  For an identifier wrapped with ShiftMapper/MultiplyMapper get the 
    //  0/1 variable representing a value. 
    public ASTNode get01var(ASTNode a, long val) {
        while(a instanceof MultiplyMapper || a instanceof ShiftMapper) {
            if(a instanceof MultiplyMapper) {
                long multiplier=a.getChild(1).getValue();
                if(val%multiplier != 0) {
                    return new BooleanConstant(false);   // Non-integer value of division -- return false. 
                }
                val=val/multiplier;
            }
            else {
                val=val-a.getChild(1).getValue();
            }
            a=a.getChild(0);
        }
        assert a instanceof Identifier;
        String varname=varTo01.get(a.toString()).get(val);    // Look up the 01 variable.
        assert varname!=null;
        return new Identifier(m, varname);
    }
    
    //////////////////////////////////////////////////////////////////////////
    //  ILP output methods. 
    
    //////////////////////////////////////////////////////////////////////////
    //  ILP output of variables.
    //  0/1 variables already generated when required -- mapping to set of 0/1 
    //  variables is in m.ilp
    
    public static void toMIPBounds(BufferedWriter b, Model m) throws IOException {
        //  For each variable that is not 0/1 or bool, output bounds. 
        categoryentry c = m.global_symbols.category_first;
        while (c != null) {
            if (c.cat == ASTNode.Decision || c.cat == ASTNode.Auxiliary) {
                Intpair bnds=m.global_symbols.getDomain(c.name).getBounds();
                if(bnds.lower!=0 || bnds.upper!=1) {
                    b.append(String.valueOf(bnds.lower));
                    b.append(" <= ");
                    b.append(c.name);
                    b.append(" <= ");
                    b.append(String.valueOf(bnds.upper));
                    b.append("\n");
                }
            }
            
            c = c.next;
        }
    }
    
    public static void toMIPGenerals(BufferedWriter b, Model m) throws IOException {
        //  For each variable that is not 0/1 or bool, output bounds. 
        categoryentry c = m.global_symbols.category_first;
        while (c != null) {
            if (c.cat == ASTNode.Decision || c.cat == ASTNode.Auxiliary) {
                Intpair bnds=m.global_symbols.getDomain(c.name).getBounds();
                if(bnds.lower!=0 || bnds.upper!=1) {
                    b.append(c.name);
                    b.append(" ");
                }
            }
            
            c = c.next;
        }
    }
    
    public static void toMIPBinary(BufferedWriter b, Model m) throws IOException {
        //  For each variable that is not 0/1 or bool, output bounds. 
        categoryentry c = m.global_symbols.category_first;
        while (c != null) {
            if (c.cat == ASTNode.Decision || c.cat == ASTNode.Auxiliary) {
                Intpair bnds=m.global_symbols.getDomain(c.name).getBounds();
                if(bnds.lower==0 && bnds.upper==1) {
                    b.append(c.name);
                    b.append(" ");
                }
            }
            
            c = c.next;
        }
    }
}
