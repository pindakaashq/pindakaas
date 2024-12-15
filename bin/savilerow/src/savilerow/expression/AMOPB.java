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
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.TreeSet;

import gnu.trove.map.hash.TIntIntHashMap;
import savilerow.*;
import savilerow.mdd.*;
import savilerow.model.*;
import savilerow.pb.*;
import savilerow.solver.*;
import savilerow.treetransformer.*;

//  Pseudo-boolean with at-most-one groups constraint. 
//  Third child is a number to control the encoding: 0-> tree, 1-> MDD, 2 GPW, 3 SWC, 4 GGT, 5 RGGT, 6 GGTH
//  Fourth child is false for ineq, true for equality. 

public class AMOPB extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    
    public boolean fromPB;  // Was this created from a PB constraint? (Otherwise from an integer sum ct)
    
    public AMOPB(ASTNode mat, ASTNode k, ASTNode enc, boolean _fromPB) {
        super(mat, k, enc, new BooleanConstant(false));   
        fromPB=_fromPB;
    }
    
    public AMOPB(ASTNode mat, ASTNode k, ASTNode enc, ASTNode equality, boolean _fromPB) {
        super(mat, k, enc, equality);
        fromPB=_fromPB;
    }
    
    public ASTNode copy() {
        return new AMOPB(getChild(0), getChild(1), getChild(2), getChild(3), fromPB);
    }
    
    public boolean isRelation() {
        return true;
    }
    
    public ASTNode simplify() {
        return simplify(true);
    }
    
    public ASTNode simplify(boolean removeZeros) {
        //  removeZeros=false when simplifying an EOPB ct. Keep the 0-weighted terms to maintain the EO property. 
        if(getChild(0).isMatrixLiteral() && getChild(1).isConstant()) {
            //  Filter out assigned terms in each group, and get UB of each group.
            ArrayList<ASTNode> ch = getChild(0).getChildren(1);
            long k=getChild(1).getValue();
            boolean changed = false;        // has it changed?
            
            // First scan for assigned variables and remove them. 
            for(int i=0; i<ch.size(); i++) {
                ASTNode coeffs_group=ch.get(i).getChild(1);
                ASTNode bools_group=ch.get(i).getChild(2);
                
                if(coeffs_group.numChildren()==1) {
                    // No terms in this group -- remove it. 
                    ch.remove(i);
                    i--;
                    changed=true;
                    continue;
                }
                
                if(coeffs_group.getCategory()>ASTNode.Constant) {
                    return null;   // Must delay. 
                }
                
                for(int j=1; j<bools_group.numChildren(); j++) {
                    ASTNode boolvar=bools_group.getChild(j);
                    long coeff=coeffs_group.getChild(j).getValue();
                    
                    if(boolvar.isConstant() && boolvar.getValue()==1) {
                        // Remove the group.
                        ch.remove(i);  // quadratic.
                        i--;
                        k=k-coeff;
                        changed=true;
                        break;
                    }
                    else if((boolvar.isConstant() && boolvar.getValue()==0) || (coeff==0L && removeZeros) ) {
                        // Term has value 0. 
                        if(coeffs_group.numChildren()==2) {
                            // Only one term in group. Remove the group.
                            ch.remove(i);
                            i--;
                            changed=true;
                            break;
                        }
                        else {
                            //  Remove the one term
                            ArrayList<ASTNode> coeffs_list=ch.get(i).getChild(1).getChildren(1);
                            ArrayList<ASTNode> bools_list=ch.get(i).getChild(2).getChildren(1);
                            coeffs_list.remove(j-1);
                            bools_list.remove(j-1);
                            coeffs_group=CompoundMatrix.make(coeffs_list);
                            bools_group=CompoundMatrix.make(bools_list);
                            ch.set(i, CompoundMatrix.make(coeffs_group, bools_group));
                            j--;
                            changed=true;
                        }
                    }
                }
            }
            
            if(k<0) {
                //  k can be reduced in the pass above, and if it goes below 0 then the ct is unsatisfiable. 
                return new BooleanConstant(false);
            }
            
            long ub=0L;
            for(int i=0; i<ch.size(); i++) {
                ASTNode coeffs_group=ch.get(i).getChild(1);
                ASTNode bools_group=ch.get(i).getChild(2);
                
                long ubgroup=0L;
                
                for(int j=bools_group.numChildren()-1; j>=1; j--) {
                    long coeff=coeffs_group.getChild(j).getValue();
                    if(coeff>ubgroup) {
                        ubgroup=coeff;
                    }
                }
                ub+=ubgroup;
            }
            
            if(ub<=k) {
                // Constraint is implied. 
                return new BooleanConstant(true);
            }
            
            long k2=factorOutGCD(ch, k);
            if(k2<k) {
                changed=true;
                k=k2;
            }
            
            if(changed) {
                getChild(0).detachChildren();
                return new AMOPB(CompoundMatrix.make(ch), NumberConstant.make(k), getChild(2), getChild(3), fromPB);
            }
        }
        return null;
    }
    
    private long factorOutGCD(ArrayList<ASTNode> ch, long k) {
        // Calculate the GCD of the coefficients and divide it out. 
        // Changes ch in place and returns k. 
        boolean containsOne=false;
        
        for(int i=0; i<ch.size() && !containsOne; i++) {
            ASTNode coeffs=ch.get(i).getChild(1);
            for(int j=1; j<coeffs.numChildren() && !containsOne; j++) {
                if(coeffs.getChild(j).getValue()==1L) {
                    containsOne=true;
                }
            }
        }
        
        long lgcd;
        if(containsOne || ch.size()==0 || ch.get(0).getChild(1).numChildren()<=1) {
            lgcd=1;
        }
        else {
            BigInteger gcd=BigInteger.valueOf(ch.get(0).getChild(1).getChild(1).getValue());
            
            for(int i=0; i<ch.size(); i++) {
                ASTNode coeffs=ch.get(i).getChild(1);
                for(int j=1; j<coeffs.numChildren(); j++) {
                    gcd=gcd.gcd(BigInteger.valueOf(coeffs.getChild(j).getValue()));
                }
            }
            
            if(getChild(3).getValue()==1) {
                //  It is an equality -- include k in the gcd calculation
                gcd=gcd.gcd(BigInteger.valueOf(k));
            }
            
            lgcd=gcd.longValue();
        }
        
        if(lgcd>1) {
            // Divide through by the GCD.
            for(int i=0; i<ch.size(); i++) {
                ASTNode coeffs=ch.get(i).getChild(1);
                for(int j=1; j<coeffs.numChildren(); j++) {
                    coeffs.setChild(j, NumberConstant.make(coeffs.getChild(j).getValue()/lgcd)); // technically shouldn't do this.
                }
            }
            
            // truncating division of k. 
            return k/lgcd;
        }
        return k;
    }
    
    @Override
    public int polarity(int child) {
        if(getChild(3).getValue()==0) {
            return -polarity();   // Reduces upper bound (when ppol is 1, i.e. constraint posted) 
        }
        else {
            return 0;  // mixed polarity
        }
    }
    
    //  To be called from a special pass before SATLiterals are introduced. 
    public ASTNode collectAMOGroups(Model m) {
        if(! CmdFlags.amo_detect) {
            return new BooleanConstant(true);
        }
        
        //  Find bool/int(0..1) variables for which we need to find AMO groups. 
        TreeSet<String> loose_bools=new TreeSet<String>();
        HashMap<String, ASTNode> loose_coeffs=new HashMap<String, ASTNode>();
        HashMap<String, Boolean> loose_neg=new HashMap<String, Boolean>();
        
        for(int i=1; i<getChild(0).numChildren(); i++) {
            ASTNode bools_ast=getChild(0).getChild(i).getChild(2);
            if(bools_ast.numChildren()==2) {
                ASTNode ch=bools_ast.getChild(1);
                
                if(ch instanceof Identifier || (ch instanceof Negate && ch.getChild(0) instanceof Identifier)) {
                    Intpair bnds=ch.getBounds();
                    if(ch.isRelation() || (bnds.lower==0 && bnds.upper==1) ) {
                        boolean negated=ch instanceof Negate;
                        if(negated) {
                            ch=ch.getChild(0);      //  Strip off negation, will restore later.
                        }
                        loose_bools.add(ch.toString());
                        loose_coeffs.put(ch.toString(), getChild(0).getChild(i).getChild(1).getChild(1));
                        loose_neg.put(ch.toString(), negated);
                    }
                }
            }
        }
        
        if(loose_bools.size()==0) {
            return new BooleanConstant(true);
        }
        
        // Print the mutexes between variables in this ct.
        /*System.out.println("PB:"+this);
        System.out.println(l);
        System.out.println("Mutexes:");
        for(int i=0; i<l.size(); i++) {
            for(int j=i+1; j<l.size(); j++) {
                int idx1=vartonum.get(l.get(i));
                int idx2=vartonum.get(l.get(j));
                
                if(adjlist.get(idx1).contains(idx2)) {
                    System.out.println(l.get(i)+", "+l.get(j));
                }
                if(adjlist.get(idx1).contains(-idx2)) {
                    System.out.println(l.get(i)+", -"+l.get(j));
                }
                if(adjlist.get(-idx1).contains(idx2)) {
                    System.out.println("-"+l.get(i)+", "+l.get(j));
                }
                if(adjlist.get(-idx1).contains(-idx2)) {
                    System.out.println("-"+l.get(i)+", -"+l.get(j));
                }
            }
        }*/
        
        TreeSet<String> loose_bools_copy=new TreeSet<String>(loose_bools);
        
        ArrayList<TreeSet<Integer>> cliques=AMODetect.buildCliques(loose_bools, loose_coeffs);
        
        //  Call the much more expensive MaxSAT based method of finding maximal cliques.
        //  Switched off for now. 
        /*if(cliques.size()>1 && cliques.size()<20) {
            cliquesByMaxsat(loose_bools_copy, cliques);
        }*/
        
        //  Build coeffs and bool groups again.
        
        ArrayList<ASTNode> amoproducts=getChild(0).getChildren(1);
        
        // Remove the singleton (negated) bools.
        for(int i=amoproducts.size()-1; i>=0; i--) {
            ASTNode bools_ast=amoproducts.get(i).getChild(2);
            if(bools_ast.numChildren()==2) {
                ASTNode ch=bools_ast.getChild(1);
                if(ch instanceof Negate) {
                    ch=ch.getChild(0);
                }
                
                if(loose_bools_copy.contains(ch.toString())) {
                    amoproducts.remove(i);
                }
            }
        }
        
        ArrayList<ASTNode> newcts=new ArrayList<ASTNode>();
        
        //  Add the cliques.
        for(int i=0; i<cliques.size(); i++) {
            TreeSet<Integer> clique=cliques.get(i);
            
            boolean allSignsMatch=true;   //  i.e. negative lits in clique line up with negated bools in original ct. 
            for(Integer idx : clique) {
                String varname=AMODetect.varslist.get((idx<0)?(-idx):idx);
                
                //  If negation recorded in loose_neg does not match polarity of literal here...
                if(loose_neg.get(varname)!=(idx<0)) {
                    allSignsMatch=false;
                    break;
                }
            }
            
            ArrayList<ASTNode> coeffs_group=new ArrayList<ASTNode>();
            ArrayList<ASTNode> bools_group=new ArrayList<ASTNode>();
            ArrayList<Boolean> negated_group=new ArrayList<Boolean>();
            
            if(allSignsMatch || clique.size()==1) {
                for(Integer v : clique) {
                    if(v<0) {
                        //  One negative literal in a clique should be handled as a positive literal
                        //  OR this is a negative literal matched by a negative bool in original ct. 
                        v=-v;
                    }
                    String varname=AMODetect.varslist.get(v);
                    
                    ASTNode ch=new Identifier(m, varname);
                    
                    bools_group.add(ch);
                    coeffs_group.add(loose_coeffs.get(varname));
                    negated_group.add(loose_neg.get(varname));
                }
                
                if(bools_group.size()>1) {
                    checkEO(bools_group, coeffs_group, negated_group);   // Check for an exactly-one based on an integer decision variable, and remove terms with smallest coefficient if so. 
                }
                
                for(int j=0; j<bools_group.size(); j++) {
                    bools_group.set(j, makeChild(bools_group.get(j), negated_group.get(j)));    //  If negated originally, add negation here. 
                }
                
                if(bools_group.size()>0) {
                    amoproducts.add(CompoundMatrix.make(CompoundMatrix.make(coeffs_group), CompoundMatrix.make(bools_group)));
                }
            }
            else {
                //  The more difficult case. Signs in the AMO group do not match
                //  signs in the original ct. 
                
                
                long k=getChild(1).getValue();
                
                for(Integer v : clique) {
                    if(v>0) {
                        String varname=AMODetect.varslist.get(v);
                        if(loose_neg.get(varname)) {
                            //  Variable negated in orig ct, positive in clique.
                            bools_group.add(new Identifier(m, varname));
                            coeffs_group.add(NumberConstant.make(-loose_coeffs.get(varname).getValue()));
                            negated_group.add(false);
                            k=k-loose_coeffs.get(varname).getValue();   //  Take off positive part from both sides.
                        }
                        else {
                            //  Positive in orig ct, positive in clique.
                            bools_group.add(new Identifier(m, varname));
                            coeffs_group.add(loose_coeffs.get(varname));
                            negated_group.add(false);
                        }
                    }
                    else {
                        String varname=AMODetect.varslist.get(-v);
                        
                        if(loose_neg.get(varname)) {
                            //  Negated in orig. constraint, negated in clique. 
                            bools_group.add(new Identifier(m, varname));
                            coeffs_group.add(loose_coeffs.get(varname));
                            negated_group.add(true);
                        }
                        else {
                            // coeff*(1-not(v))
                            
                            bools_group.add(new Identifier(m, varname));
                            coeffs_group.add(NumberConstant.make(-loose_coeffs.get(varname).getValue()));
                            negated_group.add(true);
                            k=k-loose_coeffs.get(varname).getValue();   //  Take off positive part from both sides.
                        }
                    }
                }
                
                setChild(1, NumberConstant.make(k));
                
                //  Makes an AMO group have positive coefficients.
                makePositive(m, newcts, amoproducts, bools_group, coeffs_group, negated_group);
            }
        }
        
        setChild(0, CompoundMatrix.make(amoproducts));
        
        //  Make some AMO constraints for the cliques.
        for(TreeSet<Integer> clique: cliques) {
            if(clique.size()>1) {
                ArrayList<ASTNode> terms=new ArrayList<ASTNode>();
                for(Integer v : clique) {
                    if(v>0) {
                        terms.add(new Identifier(m, AMODetect.varslist.get(v)));
                    }
                    else {
                        ASTNode ch=new Identifier(m, AMODetect.varslist.get(-v));
                        terms.add(makeChild(ch, true));  // Add appropriate negation here for either bool or int. 
                    }
                }
                newcts.add(new LessEqual(new WeightedSum(terms), NumberConstant.make(1)));
            }
        }
        
        return new And(newcts);
    }
    
    public void makePositive(Model m, ArrayList<ASTNode> newcts, ArrayList<ASTNode> amoproducts, ArrayList<ASTNode> bools_onevar, 
        ArrayList<ASTNode> coeffs_onevar, ArrayList<Boolean> negated_onevar) {
        if(bools_onevar.size()==1) {
            //  Easy case of a single variable
            long coeff=coeffs_onevar.get(0).getValue();
            assert coeff<0;
            long k=getChild(1).getValue();
            
            boolean isNeg=!(negated_onevar.get(0));
            
            //  negate the boolean, add |coeff| to both sides, end up with |coeff| * not(bool)
            
            setChild(1, NumberConstant.make(k+coeff));  // update k. 
            coeffs_onevar.set(0, NumberConstant.make(-coeff));
            
            bools_onevar.set(0, makeChild(bools_onevar.get(0), isNeg));  //  Add appropriate type of negation here. 
            
            amoproducts.add(CompoundMatrix.make(CompoundMatrix.make(coeffs_onevar), CompoundMatrix.make(bools_onevar)));
        }
        else {
            long k=getChild(1).getValue();
            
            //  Now do the trick with extra bool var to make it an EO
            
            Identifier aux=m.global_symbols.newAuxiliaryVariable(0,1);
            
            // For clique containing x, -y, z:  aux <-> (-x /\ y /\ -z)
            ArrayList<ASTNode> ch=new ArrayList<ASTNode>();
            for(int j=0; j<bools_onevar.size(); j++) {
                ch.add(makeChild(bools_onevar.get(j), ! (negated_onevar.get(j))));
            }
            newcts.add(new Iff(aux, new And(ch)));
            
            ArrayList<Long> coeffs_onevar_longs=new ArrayList<Long>();
            for(int j=0; j<coeffs_onevar.size(); j++) {
                coeffs_onevar_longs.add(coeffs_onevar.get(j).getValue());
            }
            
            long minvalue=Collections.min(coeffs_onevar_longs);
            
            assert minvalue<0;
            
            //  Now add -minvalue to each term and rhs.
            k=k-minvalue;
            
            for(int j=bools_onevar.size()-1; j>=0; j--) {
                if(coeffs_onevar.get(j).getValue()==minvalue) {
                    bools_onevar.remove(j);
                    coeffs_onevar.remove(j);
                    negated_onevar.remove(j);
                }
                else {
                    coeffs_onevar.set(j, NumberConstant.make(coeffs_onevar.get(j).getValue()-minvalue));
                }
            }
            
            bools_onevar.add(aux);
            coeffs_onevar.add(NumberConstant.make(-minvalue));
            negated_onevar.add(false);
            
            //  Replace bools with negated bools when negated flag set. 
            for(int j=0; j<bools_onevar.size(); j++) {
                bools_onevar.set(j, makeChild(bools_onevar.get(j), negated_onevar.get(j)));
            }
            amoproducts.add(CompoundMatrix.make(CompoundMatrix.make(coeffs_onevar), CompoundMatrix.make(bools_onevar)));
            setChild(1, NumberConstant.make(k));
        }
    }
    
    // Check for an exactly-one based on an integer decision variable, and remove terms with smallest coefficient if so.
    //  Should work for negated != terms 
    //   Need to check if Active CSE might hide pairs of = and != things from this. 
    private void checkEO(ArrayList<ASTNode> bools, ArrayList<ASTNode> coeffs, ArrayList<Boolean> negated) {
        ASTNode var=null;
        ArrayList<Intpair> vals=new ArrayList<Intpair>();
        
        for(int i=0; i<bools.size(); i++) {
            ASTNode tmp=TransformExtractBoolsInSums.inverseCache.get(bools.get(i).toString());
            //  Rewrite negated != to =.
            
            if((tmp instanceof AllDifferent) && negated.get(i) && tmp.getChild(0).numChildren()==3 && 
                (tmp.getChild(0).getChild(1).isConstant() || tmp.getChild(0).getChild(2).isConstant())) {
                tmp=new Equals(tmp.getChild(0).getChild(1), tmp.getChild(0).getChild(2));
                bools.set(i, tmp);
                negated.set(i, false);
            }
            
            //  Check the term is an = and the literal is not negated
            if(tmp!=null && 
                ( ((tmp instanceof Equals) && !(negated.get(i))) )) {
                //System.out.println("Found : "+tmp);
                ASTNode groupvar;
                long val;
                
                // Unpack the term
                ASTNode ch1=tmp.getChild(0);
                ASTNode ch2=tmp.getChild(1);
                
                if(ch1 instanceof Identifier && ch2.isConstant()) {
                    groupvar=ch1;
                    val=ch2.getValue();
                }
                else if(ch2 instanceof Identifier && ch1.isConstant()) {
                    groupvar=ch2;
                    val=ch1.getValue();
                }
                else {
                    return;   // Found something that is not var=const or const=var, so return without changing the AMO group.
                }
                
                // Check var and add value to the set. 
                if(var==null) {
                    var=groupvar;
                }
                
                if(! var.equals(groupvar)) {
                    return;  //  Found two distinct original decision variables in AMO group. 
                }
                
                vals=Intpair.union(vals, Intpair.makeList(val,val));
            }
            else {
                return;  // Found something that is not var=const so return without changing the AMO group.
            }
        }
        
        // Now check if value set covers the entire domain of the variable.
        ArrayList<Intpair> diff=Intpair.setDifference(var.getIntervalSetExp(), vals);
        if(diff.size()==0) {
            long kmin=Long.MAX_VALUE;
            
            for(int i=0; i<coeffs.size(); i++) {
                long coeff=coeffs.get(i).getValue();
                if(coeff<kmin) {
                    kmin=coeff;
                }
            }
            
            // Remove minimum k terms.
            for(int i=coeffs.size()-1; i>=0; i--) {
                long coeff=coeffs.get(i).getValue();
                if(coeff==kmin) {
                    //  Remove this term. 
                    coeffs.remove(i);
                    bools.remove(i);
                    negated.remove(i);
                }
                else {
                    //  Subtract kmin
                    coeffs.set(i, NumberConstant.make(coeffs.get(i).getValue()-kmin));
                }
            }
            
            // Adjust RHS.
            setChild(1, NumberConstant.make(getChild(1).getValue()-kmin));
        }
        else {
            //System.out.println("No EO. Variable domain: "+var.getIntervalSetExp());
        }
    }
    
    //  Apply the right kind of negation to a boolean or integer 0-1 child. 
    ASTNode makeChild(ASTNode boolvar, boolean negated) {
        if(negated) {
            if(boolvar.isRelation()) {
                return new Negate(boolvar);
            }
            else {
                //  0-1 integer variable. 
                return new Equals(boolvar, NumberConstant.make(0));
            }
        }
        else {
            return boolvar;
        }
    }
    
    ///   Not used -- find minimal clique cover by MaxSAT. 
    private void cliquesByMaxsat(TreeSet<String> loose_bools_copy, ArrayList<TreeSet<String>> cliques) {
        SymbolTable cliquest=new SymbolTable();
        
        ArrayList<String> bools_list=new ArrayList<String>(loose_bools_copy);  // Copy loose_bools into arraylist.
        
        int bound=cliques.size();
        
        //  Integer vars representing the clique that the vertex is assigned to.
        for(int i=0; i<bools_list.size(); i++) {
            cliquest.newVariable(bools_list.get(i), Intpair.makeDomain(1, bound-1, false), ASTNode.Decision);
        }
        
        Model cliquem=new Model();
        
        cliquem.setup(new BooleanConstant(true), cliquest, null, null, null, null, null);
        
        ArrayList<ASTNode> allvars=new ArrayList<ASTNode>();
        for(int i=0; i<bools_list.size(); i++) {
            allvars.add(new Identifier(cliquem, bools_list.get(i)));
        }
        
        ArrayList<ASTNode> cts=new ArrayList<ASTNode>();
        for(int i=0; i<bools_list.size(); i++) {
            for(int j=i+1; j<bools_list.size(); j++) {
                if(!edge(bools_list.get(i), bools_list.get(j))) {
                    cts.add(new AllDifferent(allvars.get(i), allvars.get(j)));
                }
            }
        }
        
        cliquest.newVariable("objvar", Intpair.makeDomain(1, bound-1, false), ASTNode.Decision);
        ASTNode objvar=new Identifier(cliquem, "objvar");
        
        cliquem.objective=new Minimising(objvar);
        
        cts.add(new ToVariable(new Max(allvars), objvar));
        
        cliquem.constraints=new Top(new And(cts));
        
        // Run it.
        // Minimal set of transformations to ram it into MaxSAT.
        
        TransformDecomposeMinMax tdmm=new TransformDecomposeMinMax(cliquem);
        cliquem.transform(tdmm);
        
        TransformToFlat tf=new TransformToFlat(cliquem, false);
        cliquem.transform(tf);
        
        cliquem.simplify();
        
        TransformCollectSATDirect tcsd=new TransformCollectSATDirect(cliquem);
        tcsd.transform(cliquem.constraints);
        
        SolEnum tmp=CmdFlags.soltype;
        CmdFlags.soltype=SolEnum.MAXSAT;
        
        assert cliquem.setupSAT(tcsd.getVarsInConstraints());   //  Create the satModel object and encode the variables.
        
        TransformSATEncoding tse=new TransformSATEncoding(cliquem);
        cliquem.constraints=tse.transform(cliquem.constraints);  // Avoid the branching on list and other things.
        
        assert cliquem.toSAT();
        
        SATSolver solver=new WMaxCDCLSolver(cliquem);
        
        try {
            solver.findSolutions("open-wbo", CmdFlags.satfile, cliquem);
        } catch (Exception e) {
            CmdFlags.errorExit("Borken: " + e);
        }
        
        CmdFlags.soltype=tmp;
        
        if(cliquem.incumbentSolution!=null) {
            ASTNode sol=cliquem.incumbentSolution;
            long optval=((Solution)sol).optval;
            
            cliques.clear();
            for(int i=0; i<optval; i++) {
                cliques.add(new TreeSet<String>());
            }
            
            for(int i=0; i<sol.numChildren(); i++) {
                String varname=sol.getChild(i).getChild(0).toString();
                long value=sol.getChild(i).getChild(1).getValue();
                if(loose_bools_copy.contains(varname)) {
                    cliques.get((int)value-1).add(varname);
                }
            }
        }
    }
    
    
    private boolean edge(String v1, String v2) {
        Integer v1label=AMODetect.vartonum.get(v1);
        Integer v2label=AMODetect.vartonum.get(v2);
        if(v1label==null || v2label==null) {
            return false;
        }
        else {
            return AMODetect.hasEdge(v1label, v2label);
        }
    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // 
    // Output methods.
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    ArrayList<ASTNode> ch=new ArrayList<ASTNode>();
	    ArrayList<Long> wts=new ArrayList<Long>();
	    
	    
	    
	    for(int i=1; i<getChild(0).numChildren(); i++) {
	        ASTNode amoproduct=getChild(0).getChild(i);
	        ch.addAll(amoproduct.getChild(2).getChildren(1));
	        
	        for(int j=1; j<amoproduct.getChild(1).numChildren(); j++) {
	            wts.add(amoproduct.getChild(1).getChild(j).getValue());
	        }
	    }
	    
        b.append("weightedsumleq([");
        for (int i =0; i < wts.size(); i++) {
            b.append(String.valueOf(wts.get(i)));
            if (i < wts.size() - 1) {
                b.append(",");
            }
        }
        b.append("],[");
        for (int i =0; i < ch.size(); i++) {
            ch.get(i).toMinion(b, false);
            if (i < ch.size() - 1) {
                b.append(",");
            }
        }
        b.append("],");
        getChild(1).toMinion(b, false);
        b.append(")");
	}
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //  SAT encoding
    
    //  Unpack the AST representation of coeffs and bools, and sort into
    //  some heuristic order before generating an encoding
    
    public static HashMap<ArrayList<Long>, Long> yCache=new HashMap<>();
    
    private void coeffsSort(ArrayList<ArrayList<Long>> X, ArrayList<ArrayList<Integer>> Q) {
        //  Reorder coeffs and X to be sorted in descending order of max (or should it be avg?) coefficient.
        long[] maxs=new long[X.size()];
        for(int i=0; i<Q.size(); i++) {
            maxs[i]=Collections.max(Q.get(i));
        }
        
        for(int i=0; i<Q.size(); i++) {
            for(int j=i+1; j<Q.size(); j++) {
                if(maxs[j] > maxs[i]) {
                    ArrayList<Integer> coeffgroup=Q.get(j);
                    Q.set(j, Q.get(i));
                    Q.set(i, coeffgroup);
                    
                    ArrayList<Long> boolgroup=X.get(j);
                    X.set(j, X.get(i));
                    X.set(i, boolgroup);
                    
                    long m=maxs[j];
                    maxs[j]=maxs[i];
                    maxs[i]=m;
                }
            }
        }
    }
    
    public Pair<ArrayList<ArrayList<Long>>, ArrayList<ArrayList<Integer>>> unpackCoeffs(Sat satModel) throws IOException {
        //  Construct the groups for the bools.
        ArrayList<ArrayList<Long>> X = new ArrayList<ArrayList<Long>>();
        ArrayList<ArrayList<Integer>> Q = new ArrayList<ArrayList<Integer>>();
        long k=getChild(1).getValue();
        
        for(int i=1; i<getChild(0).numChildren(); i++) {
            // Each entry in the outer matrix is a pair, first element
            // in the pair is a 1D matrix of coeffs, second element
            // is a 1D matrix of bool expressions
            ArrayList<Long> boolgroup=new ArrayList<Long>();
            
            ASTNode bools_ast=getChild(0).getChild(i).getChild(2);
            
            for(int j=1; j<bools_ast.numChildren(); j++) {
                long lit=bools_ast.getChild(j).directEncode(satModel, 1);
                boolgroup.add(lit);
            }
            X.add(boolgroup);
            
            ASTNode coeffs_ast=getChild(0).getChild(i).getChild(1);
            ArrayList<Integer> coeffgroup=new ArrayList<Integer>();
            for(int j=1; j<coeffs_ast.numChildren(); j++) {
                coeffgroup.add((int) coeffs_ast.getChild(j).getValue());
            }
            Q.add(coeffgroup);
        }
        
        coeffsSort(X, Q);
        
        //  Check/establish  normal form of AIJ paper. 
        //  Creates new X and Q
        
        ArrayList<ArrayList<Long>> X2=new ArrayList<>();
        ArrayList<ArrayList<Integer>> Q2=new ArrayList<>();
        
        TIntIntHashMap counts=new TIntIntHashMap();
        
        for(int i=0; i<Q.size(); i++) {
            counts.clear();
            
            ArrayList<Long> xi=X.get(i);
            ArrayList<Integer> qi=Q.get(i);
            
            assert xi.size()==qi.size();
            
            //  Set to false any variables with coefficient too large. 
            //  Remove duplicate coeffs within the group, replace with new variable.
            for(int j=0; j<xi.size(); j++) {
                if(xi.get(j)!=null) {
                    assert qi.get(j)!=null;
                    assert qi.get(j)>=0;
                    
                    if(qi.get(j)>k) {
                        //  If coefficient greater than K, the variable cannot be true. 
                        satModel.addClause(-xi.get(j));
                    }
                    else if(qi.get(j)>0) {
                        int coeff=qi.get(j);
                        
                        if(counts.containsKey(coeff)) {
                            counts.increment(coeff);
                            if(counts.get(coeff)==2) {
                                // There are more than one of coeff -- collect all and replace with a single literal
                                // Also store in the global yCache. 
                                
                                ArrayList<Long> lits=new ArrayList<>();
                                for(int l=0; l<qi.size(); l++) {
                                    if(qi.get(l)!=null && qi.get(l)==coeff) {
                                        lits.add(xi.get(l));
                                    }
                                }
                                
                                Collections.sort(lits);
                                long replx;
                                if(yCache.containsKey(lits)) {
                                    replx=yCache.get(lits);
                                }
                                else {
                                    replx=satModel.createAuxSATVariable();
                                    yCache.put(lits, replx);
                                    for(int litidx=0; litidx<lits.size(); litidx++) {
                                        satModel.addClause(-(lits.get(litidx)), replx);
                                    }
                                }
                                
                                boolean first=true;
                                for(int l=0; l<qi.size(); l++) {
                                    if(qi.get(l)!=null && qi.get(l)==coeff) {
                                        if(first) {
                                            xi.set(l, replx);
                                            first=false;
                                        }
                                        else {
                                            xi.set(l, null);
                                            qi.set(l, null);
                                        }
                                    }
                                }
                            }
                        }
                        else {
                            counts.put(coeff, 1);
                        }
                    }
                }
            }
            
            //  Replacement x and q
            ArrayList<Long> x_repl=new ArrayList<>();
            ArrayList<Integer> q_repl=new ArrayList<>();
            
            for(int j=0; j<xi.size(); j++) {
                if(xi.get(j)!=null) {
                    assert qi.get(j)!=null;
                    assert qi.get(j)>=0;
                    x_repl.add(xi.get(j));
                    q_repl.add(qi.get(j));
                }
            }
            
            if(x_repl.size()>0) {
                X2.add(x_repl);
                Q2.add(q_repl);
            }
        }
        return new Pair<>(X2, Q2);
    }
    
    //  Check a few trivial cases then do the encoding.
    
    private void SATEncode(Sat satModel, ArrayList<ArrayList<Long>> X, ArrayList<ArrayList<Integer>> Q, long k, boolean equality, long enc) throws IOException {
        assert !equality;  //  Currently none of the encodings can handle equality. 
        
        int maxsum=0;
        for(int i=0; i<Q.size(); i++) {
            maxsum+=Collections.max(Q.get(i));
        }
        
        // Trivial cases
        
        if(k<0) {
            satModel.addClause(-satModel.getTrue());
            return;
        }
        if(k==0) {
            for(int i=0; i<X.size(); i++) {
                for(int j=0; j<X.get(i).size(); j++) {
                    satModel.addClause(-X.get(i).get(j));
                }
            }
            return;
        }
        if(k>=maxsum && !equality) {
            return;
        }
        if(Q.size()<=1 && !equality) {
            //  If one group and ineq, all terms with coeff >k have already been removed. Constraint is trivially true.
            //  If no groups, k<0 has already been dealt with so ct is trivial again. 
            return;
        }
        
        long numvars=satModel.variableNumber;
        long numclauses=satModel.numClauses;
        
        //   Select encoding
        if(enc==1) {
            buildMDDEncoding(satModel, X, Q, k);
        }
        else if(enc==2) {
            buildGGPWEncoding(satModel, X, Q, k);
        }
        else if(enc==3) {
            buildSWCEncoding(satModel, X, Q, k);
        }
        else if(enc==4) {
            buildGGTEncoding(satModel, X, Q, k);
        }
        else if(enc==5) {
            buildRGGTEncoding(satModel, X, Q, k);
        }
        else if(enc==6) {
            buildGGTHEncoding(satModel, X, Q, k);
        }
        else if(enc==7) {
            buildGMTOEncoding(satModel, X, Q, k);
        }
        else if(enc==8) {
            buildGLPWEncoding(satModel, X, Q, k);
        }
        else {
            assert false : "Unknown encoding for AMO PB constraint.";
        }
        
        if(CmdFlags.rggt_stats) {
            System.err.println("c amopb;"+(satModel.variableNumber-numvars)+";"+(satModel.numClauses-numclauses));
        }
    }
    
    private void buildMDDEncoding(Sat satModel, ArrayList<ArrayList<Long>> X, ArrayList<ArrayList<Integer>> Q, long k) throws IOException {
        AMOPBMDDBuilder a=new AMOPBMDDBuilder(Q, X, (int) k, true);
        
        MDD mdd=a.getMDD();
        
        AbioMDDEncoding me=new AbioMDDEncoding(satModel);
        
        long rootlit=me.assertMDD(mdd);
        
        satModel.addClause(rootlit);
    }
    
    //  Unpack the AST representation of coeffs and bools, and sort into
    //  some heuristic order before generating an MDD. 
    private void buildGGPWEncoding(Sat satModel, ArrayList<ArrayList<Long>> X, ArrayList<ArrayList<Integer>> Q, long k) throws IOException {
        Watchdog.addAMOPBGlobalPolynomialWatchdog(Q, X, (int) k, false, satModel);
    }
    
    private void buildGLPWEncoding(Sat satModel, ArrayList<ArrayList<Long>> X, ArrayList<ArrayList<Integer>> Q, long k) throws IOException {
        Watchdog.addAMOPBLocalPolynomialWatchdog(Q, X, (int) k, satModel);
    }
    
    private void buildSWCEncoding(Sat satModel, ArrayList<ArrayList<Long>> X, ArrayList<ArrayList<Integer>> Q, long k) throws IOException {
        SWC.addAMOPBSWC(Q, X, (int) k, satModel);
    }
    
    private void buildGGTEncoding(Sat satModel, ArrayList<ArrayList<Long>> X, ArrayList<ArrayList<Integer>> Q, long k) throws IOException {
        GGT.addAMOPBGeneralizedTotalizer(Q, X, (int) k, satModel);
    }
    
    private void buildRGGTEncoding(Sat satModel, ArrayList<ArrayList<Long>> X, ArrayList<ArrayList<Integer>> Q, long k) throws IOException {
        RGGT.addAMOPBGeneralizedTotalizer(Q, X, (int) k, true, satModel);
    }
    
    private void buildGGTHEncoding(Sat satModel, ArrayList<ArrayList<Long>> X, ArrayList<ArrayList<Integer>> Q, long k) throws IOException {
        RGGT.addAMOPBGeneralizedTotalizer(Q, X, (int) k, false, satModel);
    }
    
    private void buildGMTOEncoding(Sat satModel, ArrayList<ArrayList<Long>> X, ArrayList<ArrayList<Integer>> Q, long k) throws IOException {
        GMTO.addAMOPBModuloTotalizer(Q, X, (int) k, satModel);
    }
    
    public void toSAT(Sat satModel) throws IOException {
        Pair<ArrayList<ArrayList<Long>>, ArrayList<ArrayList<Integer>>> p=unpackCoeffs(satModel);
        
        long enc=getChild(2).getValue();
        
        SATEncode(satModel, p.getFirst(), p.getSecond(), getChild(1).getValue(), getChild(3).getValue()==1, enc);
    }
}
