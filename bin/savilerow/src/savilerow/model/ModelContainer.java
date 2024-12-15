package savilerow.model;
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
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import savilerow.*;
import savilerow.expression.*;
import savilerow.solver.*;
import savilerow.treetransformer.*;

// This class controls the refinement process.

public class ModelContainer {
    
    public Model m;
    public ArrayList<ASTNode> parameters;
    
    public ModelContainer(Model _m, ArrayList<ASTNode> _parameters) {
        m = _m;
        parameters = _parameters;
    }
    
    public void process() {
        processPreamble();
        
        instancePreFlattening1();
        
        if (CmdFlags.getUsePropagate()) {
            squashDomains();
        }
        
        instancePreFlattening2(false);
        instanceFlattening(false);
        postFlattening(false);
    }
    
    // Same as process except does not run solver at the end.
    // This is to get the JVM up to speed.
    public void dryrun() {
        processPreamble();
        
        instancePreFlattening1();
        
        if (CmdFlags.getUsePropagate()) {
            squashDomains();
        }
        
        instancePreFlattening2(false);
        instanceFlattening(false);
        // postFlattening(false);
    }
    
    public void processPreamble() {
        CmdFlags.setOutputReady(false);        // Make sure we are not in 'output ready' state.
        CmdFlags.setAfterAggregate(false);
        ////////////////////////////////////////////////////////////////////////////
        // Substitute in the parameters
        
        // Process lettings, givens, wheres, and finds in order of declaration.
        ArrayDeque<ASTNode> preamble = m.global_symbols.lettings_givens;

        // The next loop will pull things out of the parameter file, so first
        // deal with the parameters -- make undef safe, simplify.
        for (int i =0; i < parameters.size(); i++) {
            ASTNode a = parameters.get(i);

            if (!a.typecheck(m.global_symbols)) {
                CmdFlags.errorExit("Failed type checking in parameter file:" + a);
            }

            TransformMakeSafe tms = new TransformMakeSafe(m);
            a = tms.transform(a);

            // Extract any extra constraints that were generated and add them to the end of the
            // preamble in a Where statement.
            ASTNode extra_cts = tms.getContextCts();
            if (extra_cts != null) {
                preamble.addLast(new Where(extra_cts));                /// What if the parameter is not used?
            }

            TransformSimplify ts = new TransformSimplify();
            a = ts.transform(a);

            // Unroll and evaluate any matrix comprehensions or quantifiers in the parameters.
            TransformQuantifiedExpression t2 = new TransformQuantifiedExpression(m);
            a = t2.transform(a);

            a = ts.transform(a);

            a = fixIndexDomainsLetting(a);            // Repair any inconsistency between the indices in a matrix and its matrix domain (if there is one).

            parameters.set(i, a);

            // Scan forward in the parameters to sub this parameter into future ones.
            ReplaceASTNode rep = new ReplaceASTNode(a.getChild(0), a.getChild(1));
            for (int j = i + 1; j < parameters.size(); j++) {
                parameters.set(j, rep.transform(parameters.get(j)));
            }
        }

        // Now go through the preamble in order.
        while (preamble.size() != 0) {
            ASTNode a = preamble.removeFirst();
            
            // Type check, deal with partial functions, simplify
            if (!a.typecheck(m.global_symbols)) {
                CmdFlags.errorExit("Failed type checking:" + a);
            }
            
            TransformMakeSafe tms = new TransformMakeSafe(m);
            a = tms.transform(a);
            
            // Extract any extra constraints generated in TransformMakeSafe.
            ASTNode extra_cts = tms.getContextCts();
            if (extra_cts != null) {
                preamble.addLast(new Where(extra_cts));
            }
            
            TransformSimplify ts = new TransformSimplify();
            a = ts.transform(a);
            
            // Process any quantifiers before simplifying again.
            TransformQuantifiedExpression t2 = new TransformQuantifiedExpression(m);
            a = t2.transform(a);
            
            a = ts.transform(a);
            
            if (a instanceof Letting) {
                a=fixIndexDomainsLetting(a);                // Repair any inconsistency between the indices in a matrix and its matrix domain (if there is one).
                processLetting(a);
            } else if (a instanceof Find) {
                processFind(a);
            } else if (a instanceof Where) {
                processWhere(a);
            } else {
                assert a instanceof Given;
                processGiven(a);
            }
        }
        
        if (parameters.size() > 0) {
            CmdFlags.warning("Number of givens in model file does not match number of lettings in parameter file.");
        }
        
        parameters = null;        // No longer needed.
        
        // Run type-checker before any transformation.
        if (!m.typecheck()) {
            CmdFlags.errorExit("Failed type checking after substituting in lettings.");
        }
        if(CmdFlags.getVerbose()) {
            CmdFlags.println("Model before undef handling:");
            CmdFlags.println(m);
        }
        
        //  Remove matrices indexed by matrices. 
        removeMatrixIndexedMatrices();
        
        if (!m.constraints.typecheck2(m.global_symbols)) {
            CmdFlags.errorExit("Failed type checking.");
        }
        
        // Deal with partial functions in the constraints/objective/branchingOn
        TransformMakeSafe tms = new TransformMakeSafe(m);
        m.transform(tms);

        // Make sure constant folding is done before the next rule.
        m.simplify();
    }
    
    ////////////////////////////////////////////////////////////////////////
    //
    // Non-class-level transformations (to Minion/Gecode/Minizinc/SAT)

    public void instancePreFlattening1() {
        if( (! CmdFlags.getMinionSNStrans()) && m.sns!=null) {
            //  If the output solver is not Minion SNS, deactivate the neighbourhood constraints early (before TQE)
            ASTNode newcons=((SNS)m.sns).deactivateEarly();
            m.constraints.getChild(0).setParent(null); // Do not copy the constraint set.
            m.constraints.setChild(0, new And(m.constraints.getChild(0), newcons));
            m.simplify();
        }
        
        // Capture comprehensions/quantifiers to be replaced with decision variables.
        TransformExistsVar tev=new TransformExistsVar(m);
        m.transform(tev);
        
        TransformQuantifiedExpression t2 = new TransformQuantifiedExpression(m);
        m.transform(t2);
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Atomise matrices of variables.
        destroyMatrices();
        
        //  Structured Neighbourhood Search
        if(m.sns!=null) {
            // Generate the bool and constraints to disable the incumbent variables
            ASTNode newcons=((SNSIncumbentMapping)m.sns.getChild(0)).makeIncumbentDisable();
            m.constraints.getChild(0).setParent(null);  // Do not copy the constraint set.
            m.constraints.setChild(0, new And(m.constraints.getChild(0), newcons));
            m.simplify();
        }
        
        ////////////////////////////////////////////////////////////////////////
        // Symmetry detection and breaking
        
        if(CmdFlags.getGraphColSymBreak()) {
            //  Highly specific value symmetry breaking for graph colouring.
            TransformGCAssignClique gc=new TransformGCAssignClique(m);
            m.transform(gc);
        }
        
        if(CmdFlags.getUseVarSymBreaking()) {
            writeModelAsJSON(m);
        }
        
        if(CmdFlags.amo_detect) {
            AMODetect.init();
        }
    }

    public void instancePreFlattening2(boolean propagate) {
        ////////////////////////////////////////////////////////////////////////
        //
        // Create element functions from matrix derefs.
        
        if(propagate || (CmdFlags.soltype!=SolEnum.MIP && (!CmdFlags.sat_matrixderef_decomp || !CmdFlags.getSattrans())) ) {
            TransformMatrixDeref t3 = new TransformMatrixDeref(m, propagate);
            m.transform(t3);
        }
        
        if(m.objective!=null) {
            processObjective(propagate);
        }
        
        //  Create bools to allow detection of mutexes between expressions in sums. 
        if(CmdFlags.amo_detect) {
            TransformExtractBoolsInSums teb=new TransformExtractBoolsInSums(m);
            m.transform(teb);
        }
        
        //  Trim element constraints
        TransformTrimElement tte=new TransformTrimElement(m);
        m.transform(tte);
        
        // Put into normal form.
        TransformNormalise tn = new TransformNormalise(m);
        m.transform(tn);
        
        ////////////////////////////////////////////////////////////////////////
        // Pre-flattening rearrangement
        
        if( (! CmdFlags.getMinionSNStrans() || propagate) && m.sns!=null) {
            //  If the output solver is not Minion SNS, remove the neighbourhood constraints, incumbent variables etc.
            ASTNode newcons=((SNS)m.sns).deactivate();
            m.constraints.getChild(0).setParent(null); // Do not copy the constraint set.
            m.constraints.setChild(0, new And(m.constraints.getChild(0), newcons));
            m.simplify();
            
            // Throw away the SNS object.
            m.sns=null;
        }
        
        // Delete redundant variables.
        if (CmdFlags.getRemoveRedundantVars()) {
            RemoveRedundantVars rrv=new RemoveRedundantVars();
            rrv.transform(m);
        }
        
        TransformEOPB teo=new TransformEOPB(m, propagate);
        m.transform(teo);
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Aggregation
        // Just Alldiff and GCC at the moment.
        
        if (CmdFlags.getUseAggregate()) {
            TransformCollectAlldiff tca = new TransformCollectAlldiff(m);
            m.transform(tca);
            
            TransformCollectGCC tcg = new TransformCollectGCC(m);
            m.transform(tcg);
        }
        CmdFlags.setAfterAggregate(true);
        
        if(CmdFlags.getUseDeleteVars() && CmdFlags.getUseAggregate()) {
            m.simplify();  // Delete vars is switched on after aggregation. 
        }
        
        TransformAlldiffExcept tae = new TransformAlldiffExcept(m);
        m.transform(tae);
        
        TransformOccurrence t35 = new TransformOccurrence();
        m.transform(t35);
        
        if (CmdFlags.getUseBoundVars() && (CmdFlags.getMiniontrans() || propagate)) {
            // Weird things to deal with Minion and BOUND variables.
            TransformForBoundVars t36 = new TransformForBoundVars(m);
            m.transform(t36);
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Add pre-flattening implied constraints.
        
        // Add implied sum constraint on card variables based on GCC.
        TransformGCCSum tgs = new TransformGCCSum(m);
        m.transform(tgs);
        
        ////////////////////////////////////////////////////////////////////////
        // Other pre-flattening optimisations
        
        //  Special pass for tabulation.
        //  First introduce linear views to avoid tabulating any expression that
        //  can be expressed with a linear view, e.g.  x+c=y  (by WeakPropagation)
        if(CmdFlags.getSattrans() && (!propagate) && (CmdFlags.make_short_tab==3 || CmdFlags.make_short_tab==4 || CmdFlags.tabulate_opt || CmdFlags.tabulate2)) {
            //  Use mappers to avoid unnecessary integer aux variables when targeting SAT. 
            //  A mapper behaves as an integer variable for SAT encoding. 
            TransformSumToShift tsts = new TransformSumToShift(m);
            m.transform(tsts);
            
            TransformProductToMult tptm = new TransformProductToMult(m);
            m.transform(tptm);
        }
        
        m.transform(tn);  //  Normalise to remove any duplicate constraints that would trigger identical scopes heuristic.
        Tabulation t= new Tabulation(m);
        t.process(propagate);
        
        TransformLexAlldiff tla=new TransformLexAlldiff(m);
        m.transform(tla);
        
        if((!CmdFlags.getSattrans()) || propagate) {
            //  Remove SafeElementOne for backends that have no output for it.
            TransformSafeElementOne tseo=new TransformSafeElementOne(m);
            m.transform(tseo);
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        // If we are generating Gecode output, decompose some reified constraints
        // Do this before flattening.
        if(CmdFlags.getFlatzinctrans() && !propagate) {
            TransformReifyAlldiff tgo1 = new TransformReifyAlldiff(m);
            m.transform(tgo1);
            
            TransformDecomposeNegativeTable tnt=new TransformDecomposeNegativeTable(m);
            m.transform(tnt);
            
            TransformDecomposeReifLex2 tdl2=new TransformDecomposeReifLex2(m);
            m.transform(tdl2);
            // More needed here.
        }
        
        if( (CmdFlags.getChuffedtrans() || CmdFlags.getOrtoolstrans()) && !propagate) {
            // Decompose AtLeast and AtMost constraints as in Chuffed's mznlib.
            TransformOccurrenceToSum tots=new TransformOccurrenceToSum();
            m.transform(tots);
            
            //  Decompose GCC
            TransformGCCToSums tgts=new TransformGCCToSums();
            m.transform(tgts);
        }
        
        TransformDecomposeCumulative tdc = new TransformDecomposeCumulative(propagate);
        m.transform(tdc);
        
        if(CmdFlags.getOrtoolstrans() && !propagate) {
            //  Decompose lex
            TransformDecomposeLex2 tdl=new TransformDecomposeLex2(m);
            m.transform(tdl);
        }
        
        if(CmdFlags.getFlatzinctrans() && !(CmdFlags.getGecodetrans() || CmdFlags.getChuffedtrans() || CmdFlags.getOrtoolstrans())) {
            //  Generic flatzinc
            // Decompose AtLeast and AtMost constraints
            TransformOccurrenceToSum tots=new TransformOccurrenceToSum();
            m.transform(tots);
            
            //  Same for GCC
            TransformGCCToSums tgts=new TransformGCCToSums();
            m.transform(tgts);
            
            //  Decompose allDiff
            TransformDecomposeAlldiff tda=new TransformDecomposeAlldiff(m);
            m.transform(tda);
            
            //  Decompose lex
            TransformDecomposeLex2 tdl=new TransformDecomposeLex2(m);
            m.transform(tdl);
        }
        
        if(CmdFlags.getSattrans() && !propagate) {
            //  Use mappers to avoid unnecessary integer aux variables when targeting SAT. 
            //  A mapper behaves as an integer variable for SAT encoding. 
            TransformSumToShift tsts = new TransformSumToShift(m);
            m.transform(tsts);
            
            TransformProductToMult tptm = new TransformProductToMult(m);
            m.transform(tptm);
        }
        
        // Some reformulations will be affected by order, so normalise.
        TransformNormalise tnr = new TransformNormalise(m);
        m.transform(tnr);
        
    }
    
    public void processObjective(boolean propagate) {
        //  If lex objective and target is not Minion, turn into a sum.
        ASTNode ob = m.objective.getChild(0);
        
        if(!CmdFlags.getMiniontrans() && !propagate && ob.getDimension()>0) {
            ASTNode sum=ob.getChild(1);
            
            for(int i=2; i<ob.numChildren(); i++) {
                Intpair bnds=ob.getChild(i).getBounds();
                
                ASTNode multiple=NumberConstant.make(bnds.upper-bnds.lower+1);
                
                sum=new WeightedSum(new Times(sum, multiple), ob.getChild(i));
            }
            ob=sum;
            m.objective.setChild(0, ob);
        }
        
        if(ob.getDimension()>0) {
            assert ob instanceof CompoundMatrix;
            for(int i=1; i<ob.numChildren(); i++) {
                ASTNode ob_inner=ob.getChild(i);
                //  ob_inner may need to be extracted
                processObjective1(propagate, ob_inner);
            }
        }
        else {
            processObjective1(propagate, ob);
        }
    }
    
    public void processObjective1(boolean propagate, ASTNode ob) {
        ////////////////////////////////////////////////////////////////////////
        //
        // If objective function is not a solitary variable, do one flattening op on it.
        
        if (!ob.isConstant() && ! (ob instanceof Identifier)) {
            boolean flatten = true;
            if (ob instanceof MatrixDeref || ob instanceof SafeMatrixDeref) {
                flatten = false;
                for (int i =1; i < ob.numChildren(); i++) {
                    if (! ob.getChild(i).isConstant()) {
                        flatten = true;
                    }
                }
            }
            
            if(flatten && (!propagate) && CmdFlags.getMaxsattrans() && m.objective.getChild(0) instanceof WeightedSum) {
                //  Turn it into a special type to protect the sum (but not its terms) from later passes.
                ArrayList<ASTNode> container=new ArrayList<ASTNode>();
                ASTNode sum=m.objective.getChild(0);
                for(int i=0; i<sum.numChildren(); i++) {
                    container.add(new MultiplyMapper(sum.getChild(i), NumberConstant.make(((WeightedSum)sum).getWeight(i))));
                }
                ob.getParent().setChild(ob.getChildNo(),  new MaxSATObjective(container));
                
                flatten=false;
            }
            
            if (flatten) {
                ASTNode auxvar = m.global_symbols.newAuxHelper(ob);
                
                ASTNode flatcon;
                if(CmdFlags.getAuxNonFunctional() && m.objective.getChild(0) instanceof WeightedSum && CmdFlags.getSattrans()) {
                    //  Risk-averse for now -- only do non-functional aux if targeting SAT
                    if(m.objective instanceof Minimising) {
                        flatcon = new LessEqual(ob, auxvar);
                    }
                    else {
                        flatcon = new LessEqual(auxvar, ob);
                    }
                }
                else {
                    flatcon = new ToVariable(ob, auxvar);
                }
                m.global_symbols.auxVarRepresentsConstraint(auxvar.toString(), ob.toString());
                
                // Replace ob with auxvar wherever ob is attached. 
                ob.getParent().setChild(ob.getChildNo(), auxvar);
                
                m.constraints.getChild(0).setParent(null);   //  Do not copy the constraint set.
                m.constraints.setChild(0, new And(flatcon, m.constraints.getChild(0)));
            }
        }
        
    }

    // can be executed after instancePreFlattening1
    public void squashDomains() {
        Model ipf1 = m.copy();        // Take a copy of the model
        Model verboseCopy=null;
        if(CmdFlags.getVerbose()) {
            verboseCopy=m.copy();
        }
        
        boolean tmp_outready = CmdFlags.getOutputReady();
        boolean tmp_afteragg = CmdFlags.getAfterAggregate();
        
        instancePreFlattening2(true);
        instanceFlattening(true);
        ArrayList<ASTNode> newfinds = postFlattening(true);
        
        // Rescue the FilteredDomainStore object, containing mappings from expressions to aux var names 
        FilteredDomainStore filt=m.filt;
        ASTNode isol=m.incumbentSolution;
        
        // Restore the model.
        m = ipf1;
        
        // Restore the FilteredDomainStore object. 
        m.filt=filt;
        m.incumbentSolution=isol;
        
        // Restore the control flags to their original state (flags should probably eventually be in the model.)
        CmdFlags.setOutputReady(tmp_outready);
        CmdFlags.setAfterAggregate(tmp_afteragg);
        
        // Apply reduced domains in newfinds to the symbol table.
        for (int i =0; i < newfinds.size(); i++) {
            ASTNode id = newfinds.get(i).getChild(0);
            ASTNode dom = newfinds.get(i).getChild(1);
            assert id instanceof Identifier;
            assert dom.isFiniteSet();
            
            String idname = id.toString();
            
            if (m.global_symbols.getCategory(idname) == ASTNode.Decision) {
                ASTNode olddom = m.global_symbols.getDomain(idname);
                ASTNode newdom = new Intersect(olddom, dom);
                
                // Intersect correctly casts a boolean set to an integer set when
                // intersecting it with a set of int. Sort out the boolean case.
                // This is a rather unpleasant hack.
                if (olddom.isBooleanSet()) {
                    TransformSimplify ts = new TransformSimplify();
                    newdom = Intpair.makeDomain((ts.transform(newdom)).getIntervalSet(), true);
                }
                m.global_symbols.setDomain(idname, newdom);
            }
            else {
                // It is not a primary decision variable, it should be an aux variable. 
                // Store for use if the same aux var is made again. 
                
                m.filt.auxVarFilteredDomain(idname, dom);
            }
        }
        
        if(m.sns!=null && CmdFlags.getMinionSNStrans()) {
            //  Copy filtered domains over to incumbent variables as well as primary variables.
            ASTNode primaries=m.sns.getChild(0).getChild(0);
            ASTNode incumbents=m.sns.getChild(0).getChild(1);
            assert primaries instanceof CompoundMatrix;
            assert incumbents instanceof CompoundMatrix;
            
            for(int i=1; i<primaries.numChildren(); i++) {
                String primname=primaries.getChild(i).toString();
                String incumname=incumbents.getChild(i).toString();
                
                ASTNode primary_dom = m.global_symbols.getDomain(primname);
                ASTNode newdom = new Intersect(primary_dom, m.global_symbols.getDomain(incumname));
                
                // If the old domain of the incumbent was boolean, the replacement must be boolean.
                if (m.global_symbols.getDomain(incumname).isBooleanSet()) {
                    TransformSimplify ts = new TransformSimplify();
                    newdom = Intpair.makeDomain((ts.transform(newdom)).getIntervalSet(), true);
                }
                m.global_symbols.setDomain(incumname, newdom);
            }
        }
        
        m.simplify();        // Simplifies everything with the symbol table going before the constraints.
        
        if(CmdFlags.getVerbose() && !m.equals(verboseCopy)) {
            System.out.println("Domain filtering changed model:\n"+m.toString());
        }
    }
    
    // Propagate is for shrinking domains, and will return find statements for the
    // reduced domains.
    public void instanceFlattening(boolean propagate) {
        
        //  Undef handling for solvers that have no 'safe' constraints
        if((CmdFlags.getFlatzinctrans() || CmdFlags.getMinizinctrans()) && !propagate) {
            TransformRemoveSafeTypes tfzn=new TransformRemoveSafeTypes(m);
            m.transform(tfzn);
        }
        
        if (CmdFlags.getVerbose()) {
            System.out.println("Rules: Normalisation and CSE");
        }
        
        //  Add implied sum constraints based on AllDiffs and GCCs. Only when using AC-CSE.
        TransformAlldiffGCCSum tags = new TransformAlldiffGCCSum(m);
        if(CmdFlags.getUseACCSE() || CmdFlags.getUseACCSEAlt()) {
            //  Note: when backend is Chuffed, already decomposed the GCC.  
            m.transform(tags);
        }
        
        // Sort expressions to help CSE.  This also helps with n-ary CSE by
        // sorting sub-expressions within the N-ary expression.
        TransformNormalise tnr = new TransformNormalise(m);
        
        // CSE in N-ary cts   --- *
        if (CmdFlags.getUseACCSE()) {
            m.transform(tnr);
            // Do N-ary * first.  Needs to be done before TransformTimes.
            // Unfortunately doing this early leads to possibility of making
            // an aux var, then finding (after some other CSEs) it is only used in one place.
            // Perhaps need a reverse flattening transform to deal with this.
            ACCSE c = new ACCSE();
            c.flattenCSEs(m, "*");
            CmdFlags.stats.put("AC-CSE-Times_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-Times_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-Times_total_size", c.totallength);
            m.simplify();
            
            c.flattenCSEs(m, "xor");
            CmdFlags.stats.put("AC-CSE-Xor_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-Xor_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-Xor_total_size", c.totallength);
            m.simplify();
        }
        
        if (CmdFlags.getUseACCSEAlt()) {
            // Araya, Trombettoni and Neveu algorithm.
            m.transform(tnr);            // Normalise again.

            ICSEProduct cp = new ICSEProduct();

            cp.flattenCSEs(m);
            m.simplify();
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Before flattening, deal with N-ary Times which can't appear in the output.
        // Needs to be done before plain CSE because it can cause  e.g.  ab  and abc
        // to have a standard CSE when N-ary CSE is switched off.
        CmdFlags.setOutputReady(true);
        
        TransformTimes ttimes = new TransformTimes(m);
        m.transform(ttimes);
        
        TransformXor txor = new TransformXor(m);
        m.transform(txor);
        
        // Plain CSE  -- Just top level constraints.
        if (CmdFlags.getUseCSE()) {
            m.transform(tnr);            // Normalise again. May not be necessary.
            
            CSETopLevel ctl = new CSETopLevel();
            ctl.flattenCSEs(m);
            CmdFlags.stats.put("CSETopLevel_number", ctl.numcse);
            CmdFlags.stats.put("CSETopLevel_eliminated_expressions", ctl.countcse);
            CmdFlags.stats.put("CSETopLevel_total_size", ctl.totallength);
            m.simplify();
        }
        
        // Subset N-ary CSE. Do this before plain CSE because otherwise NaryCSE
        // will only be able to take out subsets of aux variables.
        if (CmdFlags.getUseACCSE() || (this instanceof DominanceModelContainer && CmdFlags.compressDominance)) {
            ACCSE c = new ACCSE();
            
            m.transform(tnr);
            c.flattenCSEs(m, "\\/");
            CmdFlags.stats.put("AC-CSE-Or_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-Or_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-Or_total_size", c.totallength);
            m.simplify();
            
            m.transform(tnr);
            c.flattenCSEs(m, "/\\");
            CmdFlags.stats.put("AC-CSE-And_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-And_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-And_total_size", c.totallength);
            m.simplify();
            
            m.transform(tnr);
            
            if(CmdFlags.getUseActiveACCSE()) {
                ACCSEActiveSum c2=new ACCSEActiveSum();
                c2.flattenCSEs(m);
                CmdFlags.stats.put("Active-AC-CSE-Sum_number", c2.numcse);
                CmdFlags.stats.put("Active-AC-CSE-Sum_eliminated_expressions", c2.countcse);
                CmdFlags.stats.put("Active-AC-CSE-Sum_total_size", c2.totallength);
                CmdFlags.stats.put("Active-AC-CSE-Found", c2.active_ac_cs_found?1:0);
            }
            else if(CmdFlags.getUseActiveACCSE2()) {
                ACCSEActiveSum2 c2=new ACCSEActiveSum2();
                c2.flattenCSEs(m);
                CmdFlags.stats.put("Active-AC-CSE-Sum_number", c2.numcse);
                CmdFlags.stats.put("Active-AC-CSE-Sum_eliminated_expressions", c2.countcse);
                CmdFlags.stats.put("Active-AC-CSE-Sum_total_size", c2.totallength);
                CmdFlags.stats.put("Active-AC-CSE-Found", c2.active_ac_cs_found?1:0);
            }
            else {
                c.flattenCSEs(m, "+");
                CmdFlags.stats.put("AC-CSE-Sum_number", c.numcse);
                CmdFlags.stats.put("AC-CSE-Sum_eliminated_expressions", c.countcse);
                CmdFlags.stats.put("AC-CSE-Sum_total_size", c.totallength);
            }
        }
        
        if (CmdFlags.getUseACCSEAlt()) {
            //  Use X-CSE for disjunction and conjunction.
            ACCSE c = new ACCSE();
            
            m.transform(tnr);
            c.flattenCSEs(m, "\\/");
            CmdFlags.stats.put("AC-CSE-Or_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-Or_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-Or_total_size", c.totallength);
            m.simplify();
            
            m.transform(tnr);
            c.flattenCSEs(m, "/\\");
            CmdFlags.stats.put("AC-CSE-And_number", c.numcse);
            CmdFlags.stats.put("AC-CSE-And_eliminated_expressions", c.countcse);
            CmdFlags.stats.put("AC-CSE-And_total_size", c.totallength);
            m.simplify();
            
            // Araya, Trombettoni and Neveu algorithm for sums only.
            m.transform(tnr);            // Normalise again.
            ICSESum c2 = new ICSESum();
            
            c2.flattenCSEs(m);
            m.simplify();
            
            // Doesn't do the stats yet.
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        // Remove redundant constraints that were added earlier, derived from AllDiff or GCC
        // if they were not modified by AC-CSE.
        
        if(CmdFlags.getUseACCSE() || CmdFlags.getUseACCSEAlt()) {
            //  Delete implied sum constraints based on AllDiffs and GCCs that were not
            //  changed by AC-CSE. Only when using AC-CSE
            tags.removeImpliedConstraints();
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        //   Decomposition of constraints for SAT
        
        if(CmdFlags.getSattrans() && !propagate) {
            // Decompose some of the global constraints for SAT encoding
            decomposeSatEncoding();
        }
        
        if(CmdFlags.soltype == SolEnum.MIP && !propagate) {
            decomposeMIPEncoding();
        }
        
        // Plain CSE or Active CSE.
        if (CmdFlags.getUseCSE() || CmdFlags.getUseActiveCSE()) {
            m.transform(tnr);            // Normalise again.
            
            if (CmdFlags.getUseActiveCSE()) {
                CSEActive c = new CSEActive();
                c.flattenCSEs(m);
                m.simplify();
                CmdFlags.stats.put("CSE_active_number", c.numcse);
                CmdFlags.stats.put("CSE_active_eliminated_expressions", c.countcse);
                CmdFlags.stats.put("CSE_active_total_size", c.totallength);
            } else {
                // Identical-CSE.
                CSE c = new CSE();
                c.flattenCSEs(m);
                m.simplify();
                CmdFlags.stats.put("CSE_number", c.numcse);
                CmdFlags.stats.put("CSE_eliminated_expressions", c.countcse);
                CmdFlags.stats.put("CSE_total_size", c.totallength);
            }
        }
        
        if (CmdFlags.getVerbose()) {
            System.out.println("Model may have changed by CSE. Model after rule application:\n" + m.toString());
        }
        
        // Other special cases of flattening. Probably not needed with -deletevars.
        
        TransformEqual t38 = new TransformEqual(m, propagate);
        m.transform(t38);
        
        TransformEqualConst t39 = new TransformEqualConst(propagate);
        m.transform(t39);
        
        if (CmdFlags.table_squash == 1 || CmdFlags.table_squash == 3) {
            TransformShortTableSquash tsts = new TransformShortTableSquash(m);
            m.transform(tsts);
        }
        
        if(CmdFlags.table_squash == 2 || CmdFlags.table_squash == 3) {
            TransformTableToShortTable tttst = new TransformTableToShortTable(m);
            m.transform(tttst);
        }
        
        if(CmdFlags.getSattrans() && !CmdFlags.getSMTtrans() && !propagate && CmdFlags.use_polarity) {
            //  Special polarity-aware general flattening. 
            TransformToFlatPol tf=new TransformToFlatPol(m);
            m.transform(tf);
        }
        
        ////////////////////////////////////////////////////////////////////////
        //
        // General flattening.
        
        if(CmdFlags.getSMTtrans() && !propagate) {
            TransformToFlatSMT t4 = new TransformToFlatSMT(m, propagate);
            m.transform(t4);
        }
        else {
            TransformToFlat t4 = new TransformToFlat(m, propagate);
            m.transform(t4);
        }
        
        //  Special optimisation for element constraints
        if(CmdFlags.element_gac) {
            ElementGAC egac=new ElementGAC();
            egac.transform(m);
        }
        
        //  Optimisation of tables
        if(CmdFlags.factor_encoding) {
            FactorEncoding fe=new FactorEncoding();
            fe.factorEncoding(m);
            m.simplify();
        }
        
        //  Some further flattening for flatzinc solvers
        if(CmdFlags.getFlatzinctrans() && !propagate) {
            TransformToFlatGecode tfg=new TransformToFlatGecode(m);
            m.transform(tfg);
        }
        
        // If given the flag to expand short tables, OR output solver does not have short table constraint, then
        // expand short tables to full-length table constraints. 
        if(CmdFlags.getExpandShortTab() || ((CmdFlags.getFlatzinctrans() || CmdFlags.getMinizinctrans()) && !propagate)) {
            TransformExpandShortTable test=new TransformExpandShortTable(m);
            m.transform(test);
        }
        
        ////////////////////////////////////////////////////////////////////////
        //  Remove types that have no output for specific solvers.
        
        if(CmdFlags.getChuffedtrans() && !propagate) {
            TransformModToTable tmtt=new TransformModToTable(m);
            m.transform(tmtt);
            
            // Tabulate cases of div that Chuffed does not support. 
            TransformDivToTable tdtt=new TransformDivToTable(m);
            m.transform(tdtt);
        }
        if((CmdFlags.getFlatzinctrans() || CmdFlags.getMinizinctrans()) && !propagate) {
            TransformPowToTable tptt=new TransformPowToTable(m);
            m.transform(tptt);
        }
        
        ////////////////////////////////////////////////////////////////////////
        //  Remove types that have no output to any solver. 
        
        TransformMappingToTable tmtt=new TransformMappingToTable(m);
        m.transform(tmtt);
    }
    
    public ArrayList<ASTNode> postFlattening(boolean propagate) {
        // Case split for backends
        
        ////////////////////////////////////////////////////////////////////////
        // Branch for Flatzinc output.
        if(CmdFlags.getFlatzinctrans() && !propagate) {
            fznFlattening();
            return null;
        }
        
        ////////////////////////////////////////////////////////////////////////
        // Branch for Minizinc output
        if (CmdFlags.getMinizinctrans() && !propagate) {
            minizincOutput();
            return null;
        }
        
        if(CmdFlags.soltype == SolEnum.MIP && !propagate) {
            mipOutput();
            return null;
        }
        
        ////////////////////////////////////////////////////////////////////////
        // Branch for SAT output
        if(CmdFlags.getSattrans() && !CmdFlags.getSMTtrans() && !propagate) {
            return satPrepOutput();
        }

        ////////////////////////////////////////////////////////////////////////
        // Branch for SMT output
        if(CmdFlags.getSMTtrans() && !propagate) {
            return smtPrepOutput();
        }

        ////////////////////////////////////////////////////////////////////////
        //  Minion output.

        //  Get rid of sum equal for Minion.
        TransformSumEq t5 = new TransformSumEq(propagate);
        m.transform(t5);

        if(CmdFlags.make_tab && !propagate) {
            makeTables();  //  Experimental -- iterate through scopes tabulating each one and solving separately
        }

        m.simplify();

        // Warm start for optimisation
        if(CmdFlags.getOptWarmStart() && m.objective!=null && propagate) {
            MinionSolver ws = new MinionSolver();
            try {
                Solution sol=ws.optWarmStart(m);
                if(sol!=null) {
                    // Store the solution in case no better one is found, and it
                    // is needed for output.
                    m.incumbentSolution=sol;

                    // Get the value of the optimisation variable from sol and
                    // add a new constraint
                    long optval=sol.optval;
                    ASTNode newcon;
                    ASTNode obvar=m.objective.getChild(0);
                    if(m.objective instanceof Minimising) {
                        newcon=new Less(obvar, NumberConstant.make(optval));
                    }
                    else {
                        newcon=new Less(NumberConstant.make(optval), obvar);
                    }
                    System.out.println("Adding warm start constraint: "+newcon);
                    // Bound the optimisation variable.
                    m.constraints.getChild(0).setParent(null);  // Do not copy the constraint set.
                    m.constraints.setChild(0, new And(m.constraints.getChild(0), newcon));
                    m.simplify();  // Make the top And flat again.
                }
            }
            catch(Exception e) {
            }
        }

        assert CmdFlags.minionfile != null;

        String minfilename = CmdFlags.minionfile;
        
        if(!(this instanceof DominanceModelContainer)){
            try {
                FileOutputStream fw=new FileOutputStream(minfilename);
                BufferedWriter out = new BufferedWriter(new OutputStreamWriter(fw));
                m.toMinion(out, propagate);
                out.flush();
                fw.getFD().sync();
                out.close();
            } catch (IOException e) {
                CmdFlags.errorExit("Could not open file for Minion output.");
            }
            CmdFlags.println("Created output file "+ (propagate?"for domain filtering ":"") + minfilename);
        }

        
        if (propagate) {
            MinionSolver min = new MinionSolver();
            try {
                return min.reduceDomains(CmdFlags.getMinion(), minfilename, m);
            } catch (java.io.IOException e) {
                CmdFlags.errorExit("Could not run Minion: " + e);
            } catch (java.lang.InterruptedException e2) {
                CmdFlags.errorExit("Could not run Minion: " + e2);
            }
        }
        else if (CmdFlags.getRunSolver()) {
            MinionSolver min = new MinionSolver();
            try {
                if(!(this instanceof DominanceModelContainer)){
                    if(CmdFlags.dominanceRelation) {
                        DominanceModelContainer dmc = new DominanceModelContainer(m, parameters, min);
                        dmc.process();
                    }
                    else{
                        min.findSolutions(CmdFlags.getMinion(), minfilename, m);
                    }
                }
            } catch (java.io.IOException e) {
                CmdFlags.errorExit("Could not run Minion: " + e);
            } catch (java.lang.InterruptedException e2) {
                CmdFlags.errorExit("Could not run Minion: " + e2);
            }
        }
        return null;
    }

    public ArrayList<ASTNode> satPrepOutput() {
        //  Post-flattening decomposition of some constraints. 
        decomposeSatEncodingFlat();
        
        // Final flattening pass removes ToVariable within ToVariable.
        TransformToFlatGecode tfg=new TransformToFlatGecode(m);
        m.transform(tfg);
        
        m.simplify();  // Fix problem with unit vars when outputting sat. 
        
        if(CmdFlags.test_solutions) {
            CmdFlags.checkSolModel=m.copy();
        }
        
        // Mark variables for direct or order encoding.
        TransformCollectSATDirect tcsd=new TransformCollectSATDirect(m);
        tcsd.transform(m.constraints);
        if(m.objective!=null) {
            tcsd.transform(m.objective);
        }
        
        CmdFlags.printlnIfVerbose("About to do m.setupSAT");
        
        boolean satenc=m.setupSAT(tcsd.getVarsInConstraints());   //  Create the satModel object and encode the variables.
        
        if (!satenc) {
            createInfoFiles("SAT");
        }
        
        CmdFlags.printlnIfVerbose("Done m.setupSAT");
        
        //  Do the rewrites that make SATLiterals.
        TransformSATEncoding tse=new TransformSATEncoding(m);
        m.constraints=tse.transform(m.constraints);  // Avoid the branching on list and other things.
        //m.transform(tse);
        
        if(!(this instanceof DominanceModelContainer)){
            if(CmdFlags.dominanceRelation) {
                if(!CmdFlags.getRunSolver()){
                    CmdFlags.errorExit("Solution Dominance mode only works on run-solver mode");
                }
                Solver solver = createSolver();
                DominanceModelContainer dmc = new DominanceModelContainer(m, parameters, solver);
                dmc.process();
            }
            else {
                satOutput();
            }
        }

        return null;
    }
    
    public ArrayList<ASTNode> smtPrepOutput() {

        decomposeSatEncodingFlat();
        if (CmdFlags.getUseFlat() || CmdFlags.getUseIDL() || CmdFlags.getUseUF()) {
            //  Post-flattening decomposition of some constraints.
            // Final flattening pass removes ToVariable within ToVariable.
            TransformToFlatGecode tfg=new TransformToFlatGecode(m);
            m.transform(tfg);
            m.simplify();  // Fix problem with unit vars when outputting sat.
        }

        if(CmdFlags.test_solutions) {
            CmdFlags.checkSolModel=m.copy();
        }
        
        smtTransformations();
        smtConfig();
        
        //  Do the rewrites that make SATLiterals.
        TransformSATEncoding tse=new TransformSATEncoding(m);
        m.constraints=tse.transform(m.constraints);  // Avoid the branching on list and other things.
        
        if(!(this instanceof DominanceModelContainer)){
            if(CmdFlags.dominanceRelation) {
                if(!CmdFlags.getRunSolver()){
                    CmdFlags.errorExit("Solution Dominance mode only works on run-solver mode");
                }
                Solver solver = createSolver();
                DominanceModelContainer dmc = new DominanceModelContainer(m, parameters, solver);
                dmc.process();
            }
            else {
                smtOutput();
            }
        }


        // smtOutput();

        return null;
    }

    //Essential transformations for SMT correctness
    public void smtTransformations() {

        if (CmdFlags.getUseIDL()) {
            TransformShiftToIDL toIDL = new TransformShiftToIDL(m);
            toIDL.transform(m.constraints);
        }

        // Discover the variables that need an SMT encoding
        TransformCollectSMT tcSMT = new TransformCollectSMT(m);
        tcSMT.transform(m.constraints);

        // Determine the minimum bit vector size necessary
        if (CmdFlags.getUseBV()) {
            TransformSizeBV bvSize = new TransformSizeBV(m);
            CmdFlags.setBvTraversal(true);
            bvSize.transform(m.constraints);
            CmdFlags.setBvTraversal(false);
            BitVector.determineBits();
        }
    }

    public void smtConfig() {

        // Discover the variables that need a direct encoding, in addition to the order encoding.
        // Also discover variables used in model
        TransformCollectSATDirect tcsd=new TransformCollectSATDirect(m);
        tcsd.transform(m.constraints);

        CmdFlags.printlnIfVerbose("About to do m.setupSMT");

        boolean satenc=m.setupSMT(tcsd.getVarsInConstraints());   //  Create the satModel object and encode the variables.
        if(!satenc) { createInfoFiles("SMT"); }

        CmdFlags.printlnIfVerbose("Done m.setupSMT");
    }
    
    // used by -make-tab flag
    private void makeTables() {
        // Make a table with the scope specified on the command line. 
        
        MinionSolver min = new MinionSolver();
        
        ArrayList<ASTNode> scope=new ArrayList<ASTNode>();
        
        ArrayList<ASTNode> allDecisionVars=new ArrayList<ASTNode>();
        
        categoryentry c=m.global_symbols.category_first;
        while(c!=null) {
            if(c.cat==ASTNode.Decision) {
                //   Deliberately NOT aux vars for now. 
                allDecisionVars.add(new Identifier(m, c.name));
            }
            c=c.next;
        }
        
        for(int i=0; i<CmdFlags.make_tables_scope.size(); i++) {
            scope.add(allDecisionVars.get(CmdFlags.make_tables_scope.get(i)));
        }
        
        ASTNode t=null;
        try {
            t=min.makeTable(m, scope);
        }
        catch( Exception e) {
            System.out.println(e);
            e.printStackTrace(System.out);
        }
        m.constraints.getChild(0).setParent(null);  //  Do not copy the constraints.
        m.constraints=new Top(new And(m.constraints.getChild(0), t));
        m.simplify();
    }
    
    // -make-tab, generate all scopes of a given size. 
    public void makeTableScopes() {
        processPreamble();
        
        instancePreFlattening1();
        
        if (CmdFlags.getUsePropagate()) {
            squashDomains();
        }
        
        //  Temporarily set the after aggregate flag so that variables can be 
        //  deleted/unified. 
        CmdFlags.setAfterAggregate(true);
        m.simplify();
        CmdFlags.setAfterAggregate(false);
        
        ArrayList<String> decvars=m.global_symbols.getVarNamesList();
        int scopesize=CmdFlags.make_tab_scope;
        
        System.out.println(decvars);
        System.out.println(decvars.size());
        
        if(scopesize>decvars.size()) {
            return;
        }
        
        //  Make the first scope.
        ArrayList<Integer> scope_idx=new ArrayList<Integer>(scopesize);
        ArrayList<String> scope_varnames=new ArrayList<>(scopesize);
        for(int i=0; i<scopesize; i++) {
            scope_idx.add(i);
            scope_varnames.add(decvars.get(i));
        }
        
        String infofilestem;
        if(CmdFlags.paramfile!=null) {
            infofilestem=CmdFlags.paramfile+"-";
        }
        else {
            infofilestem=CmdFlags.eprimefile+"-";
        }
        
        Model m_original=m.copy();
        while(true) {
            System.out.println(scope_idx);
            CmdFlags.make_tables_scope=scope_idx;
            
            //  Add scope to info/infor filename
            CmdFlags.infofile=infofilestem+String.join("-", scope_varnames)+".info";
            
            instancePreFlattening2(false);
            instanceFlattening(false);
            postFlattening(false);
            
            if(!incrementArrayList(scope_idx, scope_idx.size()-1, decvars.size()-1)) {
                break;
            }
            
            for(int i=0; i<scopesize; i++) {
                scope_varnames.set(i, decvars.get(scope_idx.get(i)));
            }
            
            m=m_original.copy();
        }
        
    }
    
    private boolean incrementArrayList(ArrayList<Integer> scope_idx, int incidx, int maxval) {
        if(incidx<0) {
            return false;
        }
        
        scope_idx.set(incidx, scope_idx.get(incidx)+1);
        while(scope_idx.get(incidx)>maxval) {
            // Increment the index to the left.
            if(!incrementArrayList(scope_idx, incidx-1, maxval)) {
                return false;
            }
            //  Take the value from the left and add one. 
            scope_idx.set(incidx, scope_idx.get(incidx-1)+1);
        }
        
        return true;
    }
    
    private void destroyMatrices() {
        boolean has_changed = true;
        while (has_changed) {
            has_changed = false;

            HashMap<String, ASTNode> doms = m.global_symbols.getDomains();
            Iterator<Map.Entry<String, ASTNode>> itr = doms.entrySet().iterator();
            while (itr.hasNext()) {
                Map.Entry<String, ASTNode> a = itr.next();
                if (a.getValue() instanceof MatrixDomain) {
                    if (m.global_symbols.getCategory(a.getKey()) == ASTNode.Decision) {
                        TransformMatrixToAtoms tmta = new TransformMatrixToAtoms(a.getKey(), m);
                        //m.constraints=tmta.transform(m.constraints);
                        m.transform(tmta);
                        has_changed = true;
                        break;
                    }
                }
            }
        }
    }
    
    private void removeMatrixIndexedMatrices() {
        boolean has_changed = true;
        while (has_changed) {
            has_changed = false;

            HashMap<String, ASTNode> doms = m.global_symbols.getDomains();
            Iterator<Map.Entry<String, ASTNode>> itr = doms.entrySet().iterator();
            while (itr.hasNext()) {
                Map.Entry<String, ASTNode> a = itr.next();
                if (a.getValue() instanceof MatrixDomain) {
                    if (m.global_symbols.getCategory(a.getKey()) == ASTNode.Decision) {
                        boolean has_matrix_index=false;
                        for(int i=3; i<a.getValue().numChildren(); i++) {
                            if(a.getValue().getChild(i) instanceof MatrixDomain) has_matrix_index=true;
                        }
                        if(has_matrix_index) {
                            TransformMatrixIndexedMatrix tmim = new TransformMatrixIndexedMatrix(a.getKey(), m);
                            m.transform(tmim);
                            has_changed = true;
                            break;
                        }
                    }
                }
            }
        }
    }
    
    // If the -flatzinc, -gecode or -chuffed cmdline option given
    private void fznFlattening() {
        // Flattening is done already.
        TransformSumEqToSum t1 = new TransformSumEqToSum();
        m.transform(t1);
        
        // Get rid of some reified constraints where Gecode does not implement them.
        TransformReifyMin trm = new TransformReifyMin(m);
        m.transform(trm);
        
        TransformAbsReify tar = new TransformAbsReify(m);
        m.transform(tar);
        
        //  Gecode supports reified table, other flatzinc solvers and flatzinc std do not. 
        if(CmdFlags.getFlatzinctrans() && !(CmdFlags.getGecodetrans())) {
            TransformCountToSum tcts = new TransformCountToSum();
            m.transform(tcts);
            TransformTableReify ttr = new TransformTableReify(m);
            m.transform(ttr);
        }
        
        if(CmdFlags.getFlatzinctrans() && !(CmdFlags.getGecodetrans() || CmdFlags.getChuffedtrans() || CmdFlags.getOrtoolstrans())) {
            TransformTableToElement tab=new TransformTableToElement(m);
            m.transform(tab);
        }
        
        m.simplify();
        
        // THE VERY LAST THING must be to collect bool and int vars.
        TransformCollectBool tcb = new TransformCollectBool(m);
        m.constraints=tcb.transform(m.constraints);   //  Avoid branching-on list. 
        
        try {
            FileOutputStream fw=new FileOutputStream(CmdFlags.fznfile);
            BufferedWriter out = new BufferedWriter(new OutputStreamWriter(fw));
            m.toFlatzinc(out);
            out.flush();
            fw.getFD().sync();
            out.close();
        } catch (IOException e) {
            CmdFlags.errorExit("Could not open file for flatzinc output.");
        }
        
        CmdFlags.println("Created output file " + CmdFlags.fznfile);
        
        if (CmdFlags.getRunSolver()) {
            FznSolver fz = new FznSolver();
            
            try {
                fz.findSolutions(CmdFlags.getFznSolver(), CmdFlags.fznfile, m);
            } catch (java.io.IOException e) {
                CmdFlags.errorExit("Could not run flatzinc solver: " + e);
            } catch (java.lang.InterruptedException e2) {
                CmdFlags.errorExit("Could not run flatzinc solver: " + e2);
            }
        }

    }
    
    // If the -minizinc cmdline option given
    private void minizincOutput() {
        // Flattening is done already.
        
        // THE VERY LAST THING must be to collect bool and int vars.
        TransformCollectBool tcb = new TransformCollectBool(m);
        m.transform(tcb);
        
        StringBuilder b = new StringBuilder();
        m.toMinizinc(b);

        try {
            BufferedWriter out;
            out = new BufferedWriter(new FileWriter(CmdFlags.minizincfile));
            out.append(b);
            out.close();
        } catch (IOException e) {
            CmdFlags.errorExit("Could not open file for minizinc output.");
        }
        
        CmdFlags.println("Created output file " + CmdFlags.minizincfile);
        
        if (CmdFlags.getRunSolver()) {
            MznSolver mz = new MznSolver();
            
            try {
                mz.findSolutions("minizinc", CmdFlags.minizincfile, m);
            } catch (java.io.IOException e) {
                CmdFlags.errorExit("Could not run minizinc solver: " + e);
            } catch (java.lang.InterruptedException e2) {
                CmdFlags.errorExit("Could not run minizinc solver: " + e2);
            }
        }

    }
    
    private void mipOutput() {
        decomposeMIPEncodingFlat();
        
        MIP mip=new MIP(m);
        
        mip.process();   //  Introduce 0/1 variables and domain constraints where necessary.
        
        m.simplify();
        
        try {
            FileOutputStream fw=new FileOutputStream(CmdFlags.mipfile);
            BufferedWriter out = new BufferedWriter(new OutputStreamWriter(fw));
            m.toMIP(out);
            out.flush();
            fw.getFD().sync();
            out.close();
        } catch (IOException e) {
            CmdFlags.errorExit("Could not open file for MIP output.");
        }
        
        CmdFlags.println("Created output file " + CmdFlags.mipfile);
        
    }
    
    // Decompose some constraints for SAT output. Occurs before flattening.
    private void decomposeSatEncoding() {
        
        //  Two options for alldiff -- atmost constraints or pairwise binary decomposition.
        if(CmdFlags.getSMTtrans()) {
            if(CmdFlags.SMTDecompAlldiff()) {
                if(CmdFlags.SMTPairwiseAlldiff()) {
                    TransformDecomposeAlldiff tda= new TransformDecomposeAlldiff(m);
                    m.transform(tda);
                }
                else {
                    TransformAlldiffToSums tas=new TransformAlldiffToSums(m);
                    m.transform(tas);
                }
            }
        }
        else {
            // Pure SAT translation
            TransformAlldiffToSums tas=new TransformAlldiffToSums(m);
            m.transform(tas);
        }
        
        TransformGCCToSums tgts=new TransformGCCToSums();
        m.transform(tgts);
        
        TransformCountToSum tcts=new TransformCountToSum();
        m.transform(tcts);
        
        TransformOccurrenceToSum tots=new TransformOccurrenceToSum();
        m.transform(tots);
        
        TransformDecomposeLex2 tdlx=new TransformDecomposeLex2(m);
        m.transform(tdlx);
    }
    
    //  Further decompositions that are applied after flattening/CSE.
    private void decomposeSatEncodingFlat() {
        
        // Decompose constraints made from functions by ToVariable. 
        TransformDecomposeMinMax tdmm=new TransformDecomposeMinMax(m);
        m.transform(tdmm);
        
        if(CmdFlags.sat_matrixderef_decomp) {
            // Directly decompose MatrixDeref rather than going via element. 
            TransformMatrixDerefDecomp tmdd=new TransformMatrixDerefDecomp(m);
            m.transform(tmdd);
        }
        else {
            // This may unflatten when we have a reified element ct.
            if(CmdFlags.sat_element_gac) {
                TransformElementForSAT3 tefs=new TransformElementForSAT3(m);  // Stronger one, intended to be GAC
                m.transform(tefs);
            }
            else {
                TransformElementForSAT2 tefs=new TransformElementForSAT2(m);
                m.transform(tefs);
            }
        }
        
        //  Break up sums for SAT output. 
        //  Rearrange sums to have all non-constant terms on one side of binop.
        TransformSumForSAT t1=new TransformSumForSAT();
        m.transform(t1);
        
        if(CmdFlags.getSatPBEnc()!=SumEnc.TREE || CmdFlags.getSatSumEnc()!=SumEnc.TREE) {
            //  Catch AMO-PB constraints so they can be encoded using the MDD/GPW/SWC/GGT/RGGT/GGTH encodings
            TransformSumToAMOPB tpb=new TransformSumToAMOPB(m);
            m.transform(tpb);
        }
        
        // Special cases of sum on bools.
        // sum=1, sum=0, sum<=0, sum<=1, sum<1, sum<2
        
        TransformEncodeSumSpecial tess=new TransformEncodeSumSpecial(m);
        //m.transform(tess);
        
        m.simplify();   // This should not be necessary: avoid problem with knapsack where deleted variable breaks the following pass.
        
        if (!CmdFlags.getSMTtrans() || CmdFlags.getUseIDL() || CmdFlags.getUseUF()) {
            //   Tree decomp of sum.
            if(CmdFlags.getSMTtrans()) {
                //  Version that does not introduce shift mappers for IDL/UF SMT encodings. 
                TransformBreakupSum2SMT tbs = new TransformBreakupSum2SMT(m);
                m.transform(tbs);
            }
            else {
                TransformBreakupSum2 tbs = new TransformBreakupSum2(m);
                m.transform(tbs);
            }
        }

        // Get rid of sum equal, leaving only inequalities
        TransformSumEq t5 = new TransformSumEq(false);
        m.transform(t5);

        // Rearrange sums to have all non-constant terms on one side of binop.  -- Second pass required following breakup pass.
        m.transform(t1);
        
        if(CmdFlags.getSattrans() && !CmdFlags.getSMTtrans() && CmdFlags.use_polarity) {
            //  Special polarity-aware general flattening. 
            TransformToFlatPol tf=new TransformToFlatPol(m);
            m.transform(tf);
        }
        
        if (!CmdFlags.getSMTtrans() || CmdFlags.getUseFlat() || CmdFlags.getUseIDL() || CmdFlags.getUseUF()) {
            //  TransformElementForSAT2 produces non-flat output when there is a reified element constraint.
            if(CmdFlags.getSMTtrans()) {
                TransformToFlatSMT t4=new TransformToFlatSMT(m, false);
                m.transform(t4);
            }
            else {
                TransformToFlat t4 = new TransformToFlat(m, false); // Assumes SAT output is not used for preprocessing.
                m.transform(t4);
            }
        }
    }

    // If the -sat cmdline option given
    private void satOutput() {
        boolean satenc=m.toSAT();
        
        if(!satenc) {
            createInfoFiles("SAT");
        }
        
        if(!CmdFlags.getRunSolver()) {
            if(CmdFlags.interactiveSolver){
                CmdFlags.errorExit("Interactive Solvers only works on run-solver mode");
            }
        }
        else if (!CmdFlags.dominanceRelation) {
            if(!CmdFlags.interactiveSolver) {
                CmdFlags.println("Created output SAT file " + CmdFlags.satfile);
            }
            // run solver if no dominance directly
            SATSolver solver = createSolver();
            try {
                solver.findSolutions(CmdFlags.getSatSolver(), CmdFlags.satfile, m);
            } catch (Exception e) {
                CmdFlags.errorExit("Could not run SAT solver: " + e);
            }
            
            //  Delete the dimacs file because it may be very large.
            if (!CmdFlags.getKeepDimacsFile()) {
                File f = new File(CmdFlags.satfile);
                if (f.exists()) f.delete();
                
            }
        }
    }
    
    protected void smtOutput() {
        boolean satenc=m.toSMT();
        
        if (!satenc) {
            createInfoFiles("SMT");
        }
        
        if(!CmdFlags.interactiveSolver){
            CmdFlags.println("Created output SMT file " + CmdFlags.smtfile);
        }
        if (!CmdFlags.dominanceRelation){
            if(CmdFlags.getRunSolver()) {
                SATSolver solver = createSolver();

                try {
                    solver.findSolutions(CmdFlags.getSMTSolverPath(), CmdFlags.smtfile, m);
                } catch (Exception e) {
                    CmdFlags.errorExit("Could not run SMT solver: " + e);
                }

                //  Delete the smt file because it may be very large.
                if (!CmdFlags.getKeepDimacsFile()) {
                    File f = new File(CmdFlags.smtfile);
                    if (f.exists()) f.delete();
                }
            }
        }
    }
    
    // Decompose some constraints for MIP output. Occurs before flattening.
    private void decomposeMIPEncoding() {
        TransformAlldiffToSums tas=new TransformAlldiffToSums(m);
        m.transform(tas);
        
        TransformGCCToSums tgts=new TransformGCCToSums();
        m.transform(tgts);
        
        TransformCountToSum tcts=new TransformCountToSum();
        m.transform(tcts);
        
        TransformOccurrenceToSum tots=new TransformOccurrenceToSum();
        m.transform(tots);
        
        TransformDecomposeLex2 tdlx=new TransformDecomposeLex2(m);
        m.transform(tdlx);
    }
    
    //  Decompose constraints for MIP output. Occurs after flattening.
    private void decomposeMIPEncodingFlat() {
        // Directly decompose MatrixDeref rather than going via element. 
        TransformMatrixDerefDecomp tmdd=new TransformMatrixDerefDecomp(m);
        m.transform(tmdd);
        
        // Min and max. 
    }
    
    private SATSolver createSolver(){
        SATSolver solver;
        if(CmdFlags.interactiveSolver){
            if(!CmdFlags.getRunSolver()) {
                CmdFlags.errorExit("Interactive Solvers only works on run-solver mode");
            }
            if (CmdFlags.getSMTtrans()){
                solver = ((InteractiveSMT)m.satModel).getInteractiveSolver();
            }
            else {
                solver = ((InteractiveSat)m.satModel).getInteractiveSolver(); 
            }
        }
        else if(CmdFlags.getMaxsattrans()) {
            solver=new WMaxCDCLSolver(m);
        }
        else if (CmdFlags.getSMTtrans()) {
            if (CmdFlags.usingZ3()) {
                solver = new Z3Solver(m);
            }
            else if (CmdFlags.usingBoolector()) {
                solver = new BoolectorSolver(m);
            }
            else {
                assert CmdFlags.usingYices2();
                solver = new YicesSolver(m);
            }
        }
        else {
            if(CmdFlags.getSatFamily().equals("minisat")) {
                solver=new MinisatSATSolver(m);
            }
            else if(CmdFlags.getSatFamily().equals("glucose")) {
                solver=new GlucoseSATSolver(m);
            }
            else if(CmdFlags.getSatFamily().equals("cadical") || CmdFlags.getSatFamily().equals("kissat")) {
                solver=new CadicalSATSolver(m);
            }
            else if( (CmdFlags.getSatFamily().equals("nbc_minisat_all")) || (CmdFlags.getSatFamily().equals("bc_minisat_all"))) {
                solver=new AllMinisatSATSolver(m);
            }
            else {
                assert CmdFlags.getSatFamily().equals("lingeling");
                solver=new LingelingSATSolver(m);
            }
        }

        return solver;
    }
    
    private void createInfoFiles(String encoding) {
        // Create .info and .infor files.
        Stats stats=new Stats();
        stats.putValue("SavileRowTotalTime", String.valueOf(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000));
        stats.putValue("SavileRowClauseOut", "1");
        stats.makeInfoFiles();

        CmdFlags.errorExit("Failed when writing " + encoding + " encoding to file.");
    }

    ////////////////////////////////////////////////////////////////////////////
    //
    // Deal with statements in the preamble.
    
    private void processGiven(ASTNode giv) {
        ASTNode id = giv.getChild(0);
        String idname = ((Identifier) id).getName();
        ASTNode dom = giv.getChild(1);
        
        // Insert into symbol table as a parameter, with the given domain.
        if (m.global_symbols.hasVariable(idname)) {
            CmdFlags.errorExit("Symbol " + idname + " declared more than once.");
        }
        m.global_symbols.newVariable(idname, dom, ASTNode.Parameter);
        
        int num_lettings =0;
        ASTNode param = null;
        for (ASTNode p : parameters) {
            if (((Identifier) ((Letting) p).getChildren().get(0)).getName().equals(idname)) {
                param = p;
                num_lettings++;
            }
        }
        if (num_lettings != 1) {
            CmdFlags.errorExit("Parameter ('given') variable " + idname + " is defined "+num_lettings+" times in parameter file.");
        }
        
        processLetting(param);
        parameters.remove(param);
    }
    
    private void processLetting(ASTNode let) {
        assert let instanceof Letting;
        ASTNode id = let.getChild(0);
        String idname = id.toString();
        if (m.global_symbols.hasVariable(idname) && m.global_symbols.getCategory(idname) != ASTNode.Parameter) {
            CmdFlags.errorExit("Symbol " + idname + " declared more than once.");
        }
        ASTNode value = let.getChild(1);
        
        if (value.getCategory() > ASTNode.Quantifier) {
            CmdFlags.errorExit("In statement: " + let, "Right-hand side contains an identifier that is not a constant or parameter.");
        }
        
        if(m.global_symbols.getDomain(idname)!=null) {
            //  Type checking of givens
            ASTNode domain=m.global_symbols.getDomain(idname);
            if(domain.isSet()) {
                if(value.getDimension()>0 || (domain.isBooleanSet()!=value.isRelation())) {
                    CmdFlags.errorExit("For parameter "+idname+", type of value in parameter file does not match type in given statement.");
                }
            }
            else {
                assert domain instanceof MatrixDomain;
                //  Just check value is a matrix of some sort. Type will be checked when it is inserted into constant matrix store.
                if(value.getDimension()==0) {   // != domain.numChildren()-3 || (domain.getChild(0).isBooleanSet()!=value.isRelation())) {
                    CmdFlags.errorExit("For parameter "+idname+", type of value in parameter file does not match type in given statement.");
                }
            }
        }
        
        if (value instanceof CompoundMatrix || value instanceof EmptyMatrix) {
            // Put into symbol table
            // No need for domain in letting because the matrix literal has been adjusted to be consistent with the domain in the letting.
            m.cmstore.newConstantMatrix(idname, value);
            
            // Adding a constant matrix may make some lettings appear, inferred from the dimensions.
            
            ArrayList<ASTNode> newlets = m.cmstore.makeLettingsConstantMatrix(idname);
            for (ASTNode l2 : newlets) {
                processLetting(l2);
            }
            
            // Now fit the matrix literal to the domain in the symbol table if this is possible.
            // The domain in the symbol table either came from a letting or a given.
            // If it came from the letting, we are repeating work here (unfortunate but not wrong).
            // If it came from the given, we need to do this.
            m.cmstore.correctIndicesConstantMatrix(idname, true);
        }
        else {
            // Substitute it everywhere.
            m.substitute(let.getChild(0), value.copy());
        }
    }
    
    private void processFind(ASTNode find) {
        assert find instanceof Find;
        ASTNode id = find.getChild(0);
        String idname = ((Identifier) id).getName();
        if (m.global_symbols.hasVariable(idname)) {
            CmdFlags.errorExit("Symbol " + idname + " declared more than once.");
        }
        
        if (find.getChild(1).getCategory() > ASTNode.Quantifier) {
            CmdFlags.errorExit("In statement : " + find, "Right-hand side contains an identifier that is not a constant or parameter.");
        }
        m.global_symbols.newVariable(idname, find.getChild(1), ASTNode.Decision);
    }

    private void processWhere(ASTNode a) {
        a = a.getChild(0);            // get the actual statement
        // Quantifier expressions should already have been unrolled by now.
        if (a.getCategory() > ASTNode.Quantifier) {
            CmdFlags.errorExit("In statement: where " + a, "Contains an identifier that is not a constant or parameter.");
        }
        if (! a.equals(new BooleanConstant(true))) {
            CmdFlags.errorExit("In statement: where " + a, "Does not evaluate to true.");
        }
    }
    
    // Takes a letting and repairs the index domains in the constant
    // matrix using the matrix domain in the letting (if there is one).
    // Always returns a letting without a domain.
    private ASTNode fixIndexDomainsLetting(ASTNode a) {
        if (a.numChildren() == 3) {
            ASTNode mat = a.getChild(1);
            if (mat instanceof CompoundMatrix || mat instanceof EmptyMatrix) {
                Pair<ASTNode, Boolean> p = ConstantMatrixStore.fixIndicesConstantMatrix(a.getChild(2), mat.copy());
                if (p.getSecond()) {
                    CmdFlags.warning("The index domains in the matrix literal do not match");
                    CmdFlags.warning("the given matrix domain in the following letting statement:");
                    CmdFlags.warning(String.valueOf(a));
                }
                
                return new Letting(a.getChild(0), p.getFirst());
            }
        }
        return a;
    }
    
    public ModelContainer copy() {
        Model mcopy=m.copy();
        ArrayList<ASTNode> paramcopy=new ArrayList<ASTNode>();
        TransformFixSTRef tf=new TransformFixSTRef(mcopy);
        for(int i=0; i<parameters.size(); i++) {
            paramcopy.add(tf.transform(parameters.get(i)));
        }
        return new ModelContainer(mcopy, paramcopy);
    }
    
    public void writeModelAsJSON(Model m) {
        SymmetryBreaker  s = new SymmetryBreaker ();
        s.detectAndBreakSymmetries(m);
        m.simplify();
    }
}
