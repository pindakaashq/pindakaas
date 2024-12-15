package savilerow.model;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Peter Nightingale and Gökberk Koçak.

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
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import savilerow.*;
import savilerow.expression.*;
import savilerow.solver.*;
import savilerow.treetransformer.*;

// This class controls the refinement process of dominance problems.

public class DominanceModelContainer extends ModelContainer {

    // private Model m;
    private Model parent;
    private Solver solver;

    private ASTNode incompOrderSign;
    private ASTNode incompPartialOrder;
    private ArrayList<IntegerDomainConcrete> iterDomains;

    private FileOutputStream fw;
    private BufferedWriter out;



    public DominanceModelContainer(Model _model, ArrayList<ASTNode> _parameters, Solver _solver) {
        super(_model, _parameters);
        // m = _model;
        solver = _solver;
        incompOrderSign = null;
        incompPartialOrder = null;
        iterDomains = new ArrayList<>();
        fw = null;
        out = null;
    }

    public void process(){
        preprocessIncomparability();
        try{
            processDominance();
        } catch (IOException e){
            e.printStackTrace();
            CmdFlags.errorExit("Could not process dominance problem: " + e);
        }
    }

    private void preprocessIncomparability(){
        //  Pull out the cardinality constraint from the constraint set.
        ASTNode order=null;
        ASTNode incl=DominanceRelation.incl;
        ASTNode topand=m.constraints.getChild(0);
        
        if(topand instanceof And) {
            for(int i=0; i<topand.numChildren() && (order==null || incl==null); i++) {
                if(topand.getChild(i) instanceof IncomparabilityFunction) {
                    if (CmdFlags.getSMTtrans()){
                        TransformEqualConst tse=new TransformEqualConst(true);
                        m.transform(tse); 
                    }
                    order=topand.getChild(i).getChild(0);
                    incompPartialOrder=topand.getChild(i).getChild(1);
                    //if incomp is matrix
                    if(incompPartialOrder instanceof CompoundMatrix){
                        ArrayList<ASTNode> domAfterPreprocessArray = new ArrayList<>();
                        for (int j =1; j < incompPartialOrder.numChildren(); j++) {
                            ASTNode domAfterPreprocess = m.global_symbols.getDomain( incompPartialOrder.getChild(j).toString());
                            IntegerDomainConcrete iterDomain = ((IntegerDomainConcrete) domAfterPreprocess);
                            iterDomains.add(iterDomain);
                        }
                    }
                    else{
                        ASTNode domAfterPreprocess = m.global_symbols.getDomain( incompPartialOrder.toString());
                        IntegerDomainConcrete iterDomain = ((IntegerDomainConcrete) domAfterPreprocess);
                        iterDomains.add(iterDomain);
                    }
                    topand.setChild(i, new BooleanConstant(true));
                }
            }
        }
        else if(topand instanceof IncomparabilityFunction) {
            if (CmdFlags.getSMTtrans()){
                TransformEqualConst tse=new TransformEqualConst(true);
                m.transform(tse); 
            }
            //  All other constraints have been removed
            order=topand.getChild(0);
            incompPartialOrder=topand.getChild(1);
            //if incomp is matrix
            if(incompPartialOrder instanceof CompoundMatrix){
                ArrayList<ASTNode> domAfterPreprocessArray = new ArrayList<>();
                for (int j =1; j < incompPartialOrder.numChildren(); j++) {
                    ASTNode domAfterPreprocess = m.global_symbols.getDomain( incompPartialOrder.getChild(j).toString());
                    IntegerDomainConcrete iterDomain = ((IntegerDomainConcrete) domAfterPreprocess);
                    iterDomains.add(iterDomain);
                }
            }
            else{
                ASTNode domAfterPreprocess = m.global_symbols.getDomain( incompPartialOrder.toString());
                IntegerDomainConcrete iterDomain = ((IntegerDomainConcrete) domAfterPreprocess);
                iterDomains.add(iterDomain);
            }
            m.constraints.setChild(0, new BooleanConstant(true));
        }
        
        if(order==null) {
            // CmdFlags.errorExit("Could not find IncomparabilityFunction function.");

            CmdFlags.println("Operating w/o IncomparabilityFunction. Might get dominated solutions.");
        }
        if(incl==null) {
            CmdFlags.errorExit("Could not find DominanceRelation function.");
        }
        // remove the trues. 
        m.simplify();

        // Set IncomparabilityFunction field(s)
        incompOrderSign = order;
    }

    private void processDominance() throws IOException{
        //clean the info file
        BufferedWriter out = new BufferedWriter(new FileWriter(CmdFlags.infofile, false));
        out.close();
        // initial model sat output is not done yet.
        if (CmdFlags.getSattrans() && !CmdFlags.getSMTtrans()){
            satOutput();
        }
        else if(CmdFlags.getSMTtrans()){
            smtOutput();
        }
        cleanLastLine();
        //no incomp function is given, do it the old way
        int dom_depth = 0;
        if (incompOrderSign == null){
            boolean workerFlag = true;
            while(workerFlag){
                workerFlag = processEachDominance(null, ++dom_depth);
            }
        }
        //there is incomp function
        else{
            Boolean ascOrder = incompOrderSign.getValue() == 0 ? true : false;
            List<List<Long>> collector = new ArrayList<>();
            ArrayList<Long> combo = new ArrayList<>();
            combinations(collector, iterDomains, 0, combo, ascOrder);
            for (List<Long> domValues : collector) {
                //CDP+I no block repeat trick
                if (CmdFlags.noblockDom && incompPartialOrder != null){
                    boolean repeatFlag = true;
                    while(repeatFlag){
                        processEachDominance(domValues, ++dom_depth);
                        if (DominanceRelation.sollist == null || DominanceRelation.sollist.size() == 0){
                            repeatFlag = false;
                        }
                    }
                }
                else{
                    processEachDominance(domValues, ++dom_depth);
                }
            }
        }
    }

    
    /**
     * Getting combinations of the incomp partial orders while respecting order
     * @param collector
     * @param partialOrders
     * @param n
     * @param combo
     * @param asc
     */
    private void combinations(List<List<Long>> collector, List<IntegerDomainConcrete> iterDomains, int n, List<Long> combo, Boolean asc) {
        if (n == iterDomains.size()) {
            collector.add(new ArrayList<>(combo));
            return;
        }
        for (Long l : getValuesDomainConcrete(iterDomains.get(n), asc)) {
            combo.add(l);
            combinations(collector, iterDomains, n + 1, combo, asc);
            combo.remove(combo.size() - 1);
        }
    }
    
    /**
     * Return the list contained in Domain
     * @param asc ascending order for true - descending order for false 
     * @return the list
     */
    private ArrayList<Long> getValuesDomainConcrete(IntegerDomainConcrete d, boolean asc) {
        ArrayList<Long> list = new ArrayList<>();
        long it = asc ? d.getBounds().lower : d.getBounds().upper;
        while (d.containsValue(it)){
            list.add(it);
            it = asc ? it+1 : it-1;
        }
        return list;
    }

    private boolean processEachDominance(List<Long> domValues, long dom_depth) throws IOException{
        // const
        ASTNode incompConstraint = constructIncompConstraint(domValues);
        reOpenFiles();
        boolean noTerminateFlag = encodeNewDominanceConstrainsts(dom_depth);
        if (!noTerminateFlag){
            return false;
        }   
        markModelAndClean();
        if (domValues != null){
            encodeIncompConst(incompConstraint);
        }
        finaliseAndRunSolver(domValues);
        restoreModel();
        return true;
    }

    private ASTNode constructIncompConstraint(List<Long> domValues) throws IOException{
        //incomp order constraint
        ASTNode c0 = new BooleanConstant(true);
        //if domValue is null it means incomp function doesnt exists.
        if (domValues != null){
            CmdFlags.println("Looking for solution on incomp value(s): " + domValues);
            //  Put the number into the info file. 
            BufferedWriter out= new BufferedWriter(new FileWriter(CmdFlags.infofile, true));
            out.write("Partial order: "+String.valueOf(domValues)+"\n");
            out.close();
            //  Make the new constraint for the incomp
            //  There might be single or multiple
            if (domValues.size() == 1){
                ASTNode c1 = new LessEqual(incompPartialOrder, NumberConstant.make(domValues.get(0)));
                ASTNode c2 = new LessEqual(NumberConstant.make(domValues.get(0)), incompPartialOrder);
                ASTNode[] temp = {c0, c1, c2};
                c0 = new And(temp);
            }
            else{
                for (int i = 0; i < domValues.size(); i++) {
                    ASTNode c1 = new LessEqual(incompPartialOrder.getChild(i+1), NumberConstant.make(domValues.get(i)));
                    ASTNode c2 = new LessEqual(NumberConstant.make(domValues.get(i)), incompPartialOrder.getChild(i+1));
                    ASTNode[] temp = {c0, c1, c2};
                    c0 = new And(temp);
                }
            }
            TransformSimplify ts=new TransformSimplify();
            c0 = ts.transform(c0);
        }
        return c0;
    }

    private void reOpenFiles() throws IOException{
        //  Re-open the sat file.
        if ((CmdFlags.getSattrans() || CmdFlags.getSMTtrans()) && !CmdFlags.interactiveSolver){
            m.satModel.reopenFile();
        }
        else if(solver instanceof MinionSolver){
            fw = new FileOutputStream(CmdFlags.minionfile, true);
            out = new BufferedWriter(new OutputStreamWriter(fw));
        }
    }
    
    /**
     * Clean last line depending on the solver
     */
    private void cleanLastLine() throws IOException{
        if (solver instanceof MinionSolver){
            m.BTRemoveLastLine(); 
        } 
        else if(CmdFlags.getSMTtrans()){
            ((SMT)m.satModel).removeSolvingInstructions();
        }
    }

    private void markModelAndClean() throws IOException{
        // Mark Model before encoding the incomp
        if ((CmdFlags.getSattrans() || CmdFlags.getSMTtrans()) && !CmdFlags.interactiveSolver){
            //   Commit to the above encoding of exclusion constraints.
            // m.satModel.finaliseOutput();
            m.satModel.BTMark();
        }
        if (solver instanceof MinionSolver){
            // m.finaliseOutput(out, fw);
            m.BTMark(); 
        }
        //  Clear solutions to avoid encoding them multiple times. 
        if(DominanceRelation.sollist!=null) {
            DominanceRelation.sollist.clear();
        }
    }

    private void restoreModel() throws IOException{
        if ((CmdFlags.getSattrans() || CmdFlags.getSMTtrans()) && !CmdFlags.interactiveSolver){
            //  Restore the state of the DIMACS file and the Sat object before the next iteration.
            m.satModel.BTRestore();
        }
        else if(solver instanceof MinionSolver){
            m.BTRestore();
        }
    }

    private boolean encodeNewDominanceConstrainsts(long dom_depth) throws IOException{
        //  Make the new constraints to exclude subsets of previously found itemsets with the same frequency.
        
        ASTNode incl=DominanceRelation.incl;
        if(DominanceRelation.sollist!=null && DominanceRelation.sollist.size() > 0) {
            // if previous run has 0 solution on no incomp function, terminate.
            if (incompPartialOrder == null){
                return false;
            }
            TransformQuantifiedExpression tqe=new TransformQuantifiedExpression(m);
            TransformSimplify ts=new TransformSimplify();
            HashMap<String, ASTNode> sol_hash=new HashMap<String, ASTNode>();
            //compressed dom
            ArrayList<ASTNode> domConstArray = new ArrayList<>();
            for(int i=0; i<DominanceRelation.sollist.size(); i++) {
                ASTNode sol=DominanceRelation.sollist.get(i);
                ASTNode ctcopy=incl.copy();
                for(int j=0; j<sol.numChildren(); j++) {
                    sol_hash.put(sol.getChild(j).getChild(0).toString(), sol.getChild(j).getChild(1));
                }
                //  Sub in value of X from the solution, replacing fromSolution(X) function.
                TransformSubInSolution tsis=new TransformSubInSolution(sol_hash);
                ctcopy=tsis.transform(ctcopy);
                ctcopy=ts.transform(tqe.transform(ts.transform(ctcopy)));
                // Add to dom array
                domConstArray.add(ctcopy);
            }
            // There are dom constraints.
            if(domConstArray.size() > 0){
                ASTNode domsConstraint = new Top(new And(domConstArray));
                Model subModel = prepareSubModel(domsConstraint);
                if(CmdFlags.dom_flatten_strategy.equals("full")){
                    flattenDominanceConstraintsFull(domsConstraint);
                } else if(CmdFlags.dom_flatten_strategy.equals("semi")){
                    flattenDominanceConstraintsSemi(domsConstraint);
                } else if(CmdFlags.dom_flatten_strategy.equals("basic")){
                    flattenDominanceConstraintsNaive(domsConstraint);
                }  
            }
    
        }
        // if no incomp with unsolveable problem on start, finish immediately.
        else if (incompPartialOrder == null && dom_depth != 1){
            return false;
        }
        return true;
    }

    private void flattenDominanceConstraintsNaive(ASTNode domsConstraint) throws IOException{
        TransformSATEncoding tse=new TransformSATEncoding(m);
        TransformQuantifiedExpression tqe=new TransformQuantifiedExpression(m);
        TransformSimplify ts=new TransformSimplify();
        if(!CmdFlags.compressDominance){
            if (CmdFlags.getSattrans()){
                domsConstraint=tse.transform(domsConstraint);
                //required distribute logical for or of ands
                TransformDistributeLogical tdl=new TransformDistributeLogical(false, false);
                domsConstraint=tdl.transform(domsConstraint);
                domsConstraint=ts.transform(tqe.transform(ts.transform(domsConstraint)));
                //  Encode the constraint.
                domsConstraint.toSAT(m.satModel);
                if (!CmdFlags.interactiveSolver){
                    m.satModel.finaliseOutput();
                }
            }
            else if(solver instanceof MinionSolver){
                //minion
                domsConstraint.toMinion(out, true);
                out.append("\n");
            }
            else if(CmdFlags.getSMTtrans()){
                assert(false);
            }
        } else {
            CmdFlags.errorExit("This flattening cannot do accse.");
        }
    }

    private void flattenDominanceConstraintsSemi(ASTNode domsConstraint) throws IOException{
        Model subModel = prepareSubModel(domsConstraint);
        if(CmdFlags.compressDominance){
            //ACCSE
            TransformNormalise tnr = new TransformNormalise(subModel);
            subModel.transform(tnr);
            subModel.simplify();
            ACCSE c = new ACCSE();
            c.flattenCSEs(subModel, "\\/");
            System.out.println("AC-CSE-Or_number "+ c.numcse);
            System.out.println("AC-CSE-Or_eliminated_expressions "+ c.countcse);
            System.out.println("AC-CSE-Or_total_size "+ c.totallength);
            c.flattenCSEs(subModel, "/\\");
            System.out.println("AC-CSE-And_number "+c.numcse);
            System.out.println("AC-CSE-And_eliminated_expressions "+ c.countcse);
            System.out.println("AC-CSE-And_total_size "+ c.totallength);
        }
        TransformToFlat ttf = new TransformToFlat(subModel, true);
        subModel.transform(ttf);
        // sat transform
        if (CmdFlags.getSattrans()){
            TransformCollectSATDirect subTcsd=new TransformCollectSATDirect(subModel);
            subTcsd.transform(subModel.constraints);
            TransformQuantifiedExpression tqe2=new TransformQuantifiedExpression(subModel);
            TransformDistributeLogical tdl2=new TransformDistributeLogical(false, false);
            subModel.constraints=tdl2.transform(subModel.constraints);
            TransformSimplify ts=new TransformSimplify();
            subModel.constraints=ts.transform(tqe2.transform(ts.transform(subModel.constraints)));
            //get direct encodable ones and encode them
            subModel.satModel.generateVariableEncoding(subTcsd.getVarsInConstraints(), false);
            TransformSATEncoding subtTse=new TransformSATEncoding(subModel);
            subModel.constraints=subtTse.transform(subModel.constraints);
            // subModel.simplify();
            // subModel.satModel.finaliseOutput();
            subModel.toSAT();
            //give var/clause number back
            m.satModel.variableNumber = subModel.satModel.variableNumber;
            m.satModel.numClauses += subModel.satModel.numClauses;
        }
        // minion
        else if(solver instanceof MinionSolver) {
            // subModel.branchingon = null;
            subModel.toMinion(out, false);
            out.append("\n");
        }
        else if(CmdFlags.getSMTtrans()){
            assert(false);
        }
    }

    private void flattenDominanceConstraintsFull(ASTNode domsConstraint) throws IOException{
        Model subModel = prepareSubModel(domsConstraint);
        parent = m;
        m = subModel;
        instancePreFlattening1();
        instancePreFlattening2(false);
        instanceFlattening(false);
        postFlattening(false);
        
        m = parent;
        if (CmdFlags.getSattrans() && !CmdFlags.getSMTtrans()){
            subModel.toSAT();
        }
        else if(solver instanceof MinionSolver) {
            // subModel.branchingon = null;
            subModel.toMinion(out, false);
            cleanLastLine();
            out.append("\n");
        }
        else if(CmdFlags.getSMTtrans()){
            subModel.toSMT();
        }
    }

    private Model prepareSubModel(ASTNode domConstraint){
        Model subModel = new Model();
        subModel.subModelFlag = true;
        SymbolTable newst=m.global_symbols;
        // try filter domain without copy
        // FilteredDomainStore f=m.filt;
        FilteredDomainStore f=m.filt.copy(newst);
        ConstantMatrixStore cmst=m.cmstore;
        // ASTNode preserveVariables = m.preserveVariables;
        //only new constraints
        subModel.setup(domConstraint, newst, f, cmst, null, null, null, null, null);
        if (CmdFlags.getSattrans() && !CmdFlags.interactiveSolver && !CmdFlags.getSMTtrans()){
            subModel.satModel=new Sat(m.satModel);
        }
        else if(CmdFlags.getSattrans() && CmdFlags.interactiveSolver && !CmdFlags.getSMTtrans()){
            subModel.satModel=m.satModel;
        }
        else if(CmdFlags.getSMTtrans() && !CmdFlags.interactiveSolver){
            subModel.satModel=new SMT((SMT)m.satModel);
        }
        else if(CmdFlags.getSMTtrans() && CmdFlags.interactiveSolver){
            subModel.satModel=(InteractiveSMT)m.satModel;
        }
        return subModel;
    }

    private void encodeIncompConst(ASTNode incompConst) throws IOException{
        // dont encode incomp if there is none
        if (CmdFlags.getSattrans() && !CmdFlags.interactiveSolver && !CmdFlags.getSMTtrans()){
            m.satModel.reopenFile();
            TransformSATEncoding tse=new TransformSATEncoding(m);
            incompConst=tse.transform(incompConst);
            incompConst.toSAT(m.satModel); 
            m.satModel.finaliseOutput();
        }
        else if(CmdFlags.getSMTtrans() && !CmdFlags.interactiveSolver){
            m.satModel.reopenFile();
            TransformSATEncoding tse=new TransformSATEncoding(m);
            incompConst=tse.transform(incompConst);
            incompConst.toSMT((SMT)m.satModel); 
            m.satModel.finaliseOutput();
        }
        else if(solver instanceof MinionSolver){
            fw = new FileOutputStream(CmdFlags.minionfile, true);
            out = new BufferedWriter(new OutputStreamWriter(fw));
            incompConst.toMinion(out, true);
            out.append("\n");
            m.finaliseOutput(out, fw);
        }
        else if(CmdFlags.getSattrans() && CmdFlags.interactiveSolver && !CmdFlags.getSMTtrans()){
            TransformSATEncoding tse=new TransformSATEncoding(m);
            incompConst=tse.transform(incompConst);
            assert incompConst instanceof And || incompConst instanceof SATLiteral;
            if (incompConst instanceof And){
                for(int i = 0; i < incompConst.numChildren(); i++) {
                    ASTNode child = incompConst.getChild(i);
                    assert child instanceof SATLiteral;
                    ((SATLiteral)(child)).toSATAssumption(m.satModel);
                }
            }
            else {
                ((SATLiteral)(incompConst)).toSATAssumption(m.satModel);
            }
        }
        else if(CmdFlags.getSMTtrans() && CmdFlags.interactiveSolver){
            TransformSATEncoding tse=new TransformSATEncoding(m);
            incompConst=tse.transform(incompConst);
            assert incompConst instanceof And || incompConst instanceof LessEqual;
            if (incompConst instanceof And){
                for(int i=0; i<incompConst.numChildren(); i++) {
                    ASTNode child = incompConst.getChild(i);
                    assert child instanceof LessEqual;
                    ((InteractiveSMT)m.satModel).addSMTAssumption(((LessEqual)(child)).smtEncodeBool((SMT)m.satModel));
                }
            }
            else{
                assert incompConst instanceof LessEqual;
                ((InteractiveSMT)m.satModel).addSMTAssumption(((LessEqual)(incompConst)).smtEncodeBool((SMT)m.satModel));
            }
        }
    }

    private void finaliseAndRunSolver(List<Long> domValues) throws IOException{
        try {
            //CDP+I no block repeat trick
            if (CmdFlags.getSattrans() && CmdFlags.noblockDom && incompPartialOrder != null && !CmdFlags.getSMTtrans()){
                if (!CmdFlags.interactiveSolver){
                    System.out.println("Dimacs file size: " + Files.size(Paths.get(CmdFlags.satfile ))+ " in " + domValues );
                }
                ((SATSolver)(solver)).findOneSolution(CmdFlags.getSatSolver(), CmdFlags.satfile, m);
            }
            else if (CmdFlags.getSattrans() && !CmdFlags.interactiveSolver && !CmdFlags.getSMTtrans()){
                System.out.println("Dimacs file size: " + Files.size(Paths.get(CmdFlags.satfile ))+ " in " + domValues );
                if(CmdFlags.getVerbose()) {
                    //copy file
                    Files.deleteIfExists(Paths.get(CmdFlags.satfile+"-"+domValues));
                    Files.copy(Paths.get(CmdFlags.satfile), Paths.get(CmdFlags.satfile+"-"+domValues));
                }
                solver.findSolutions(CmdFlags.getSatSolver(), CmdFlags.satfile, m);
            }
            else if (CmdFlags.getGecodetrans() || CmdFlags.getChuffedtrans()) {
                out = new BufferedWriter(new FileWriter(CmdFlags.fznfile));
                m.toFlatzinc(out);
                if(CmdFlags.getVerbose()) {
                    //copy file
                    Files.deleteIfExists(Paths.get(CmdFlags.fznfile+"-"+domValues));
                    Files.copy(Paths.get(CmdFlags.fznfile), Paths.get(CmdFlags.fznfile+"-"+domValues));
                }
                String solbin= CmdFlags.getFznSolver();
                solver.findSolutions(solbin, CmdFlags.fznfile, m);
                // System.exit(1);
            }
            else if(solver instanceof MinionSolver){
                //add last minute **EOF**
                fw = new FileOutputStream(CmdFlags.minionfile, true);
                out = new BufferedWriter(new OutputStreamWriter(fw));
                out.append("**EOF**\n");
                m.finaliseOutput(out, fw);
                System.out.println("Minion file size: " + Files.size(Paths.get(CmdFlags.minionfile ))+ " in " + domValues );
                if(CmdFlags.getVerbose()) {
                    //copy file
                    Files.deleteIfExists(Paths.get(CmdFlags.minionfile+"-"+domValues));
                    Files.copy(Paths.get(CmdFlags.minionfile), Paths.get(CmdFlags.minionfile+"-"+domValues));
                }
                //run minion for magic
                solver.findSolutions(CmdFlags.getMinion(), CmdFlags.minionfile, m); 
            }
            else if(solver instanceof InteractiveSATSolver){
                solver.findSolutions(CmdFlags.getSatSolver(), CmdFlags.satfile, m);
                // Clear assumptions
                ((InteractiveSATSolver)(solver)).cleanAssumptionQueue();
            }
            else if(CmdFlags.getSMTtrans() && !CmdFlags.interactiveSolver){
                System.out.println("SMT file size: " + Files.size(Paths.get(CmdFlags.smtfile ))+ " in " + domValues );
                if(CmdFlags.getVerbose()) {
                    //copy file
                    Files.deleteIfExists(Paths.get(CmdFlags.smtfile+"-"+domValues));
                    Files.copy(Paths.get(CmdFlags.smtfile), Paths.get(CmdFlags.smtfile+"-"+domValues));
                }
                ((SMTSolver)(solver)).findSolutions(CmdFlags.getSMTSolverPath(), CmdFlags.smtfile, m);
            }
            else if(CmdFlags.getSMTtrans() && CmdFlags.interactiveSolver){
                ((InteractiveSMTSolver)(solver)).findSolutions(CmdFlags.getSMTSolverPath(), CmdFlags.smtfile, m);
            }
        } catch (InterruptedException e) {
            CmdFlags.errorExit("Could not run the solver: " + e);
        }
    }

    private void satOutput() {
        boolean satenc=m.toSAT();    
        if(!satenc) {
            // Create .info and .infor files. 
            Stats stats=new Stats();
            stats.putValue("SavileRowTotalTime", String.valueOf(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000));
            stats.putValue("SavileRowClauseOut", "1");
            stats.makeInfoFiles();
            CmdFlags.errorExit("Failed when writing SAT encoding.");
        }
    }
}