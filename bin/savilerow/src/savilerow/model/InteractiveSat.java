package savilerow.model;
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

import java.util.ArrayList;

import savilerow.CmdFlags;
import savilerow.solver.*;

public class InteractiveSat extends Sat{

    private InteractiveSATSolver iSolver;
    
    public static long top = 100000000;
    
    public InteractiveSat(Model m){ 
        super(m.global_symbols);
        initInteractiveSolver(m);
        //make true var and add that clause as the true clause.
        trueVar=getNextVariableNumber();
        addClause(trueVar);
    }

    private void initInteractiveSolver(Model m){
        if( (CmdFlags.getSatFamily().equals("nbc_minisat_all")) || (CmdFlags.getSatFamily().equals("bc_minisat_all"))) {
            iSolver = new InteractiveAllMinisatSATSolver(m);
        }
        else if(CmdFlags.getSatFamily().equals("glucose")) {
            iSolver=new InteractiveGlucoseSATSolver(m);
        }
        else if(CmdFlags.getSatFamily().equals("cadical")){
            iSolver=new InteractiveCadicalSATSolver(m);
        }
        else{
            CmdFlags.warning("Using default SAT solver: glucose");
            iSolver = new InteractiveGlucoseSATSolver(m);
        }
        // set rnd seed if it supplied
        for(String flag : CmdFlags.getSolverExtraFlags()){
            if(flag.startsWith("seed")){
                String[] pair = flag.split("=");
                iSolver.setRndSeedToISATSolver(Long.parseLong(pair[1].trim()));
            }
        }
    }

    public InteractiveSATSolver getInteractiveSolver(){
        return iSolver;
    }

    @Override
    public void addComment(String comment){
    }  

    @Override
    public void addClause(long lit1) {
        ArrayList<Long> tempClause = new ArrayList<Long>();
        if(CmdFlags.getMaxsattrans()) {
            tempClause.add(top);
        }
        if(lit1!=-trueVar) {
            tempClause.add(lit1);
        }
        iSolver.addClauseToISATSolver(tempClause.stream().mapToLong(i -> i).toArray());
        numClauses++;
    }
    @Override
    public void addClause(long lit1, long lit2){
        ArrayList<Long> tempClause = new ArrayList<Long>();
        if(CmdFlags.getMaxsattrans()) {
            tempClause.add(top);
        }
        if(lit1!=-trueVar) {
            tempClause.add(lit1);
        }
        if(lit2!=-trueVar) {
            tempClause.add(lit2);
        }
        iSolver.addClauseToISATSolver(tempClause.stream().mapToLong(i -> i).toArray());
        numClauses++;
    }
    @Override
    public void addClause(long lit1, long lit2, long lit3){
        ArrayList<Long> tempClause = new ArrayList<Long>();
        if(CmdFlags.getMaxsattrans()) {
            tempClause.add(top);
        }
        if(lit1!=-trueVar) {
            tempClause.add(lit1);
        }
        if(lit2!=-trueVar) {
            tempClause.add(lit2);
        }
        if(lit3!=-trueVar) {
            tempClause.add(lit3);
        }
        iSolver.addClauseToISATSolver(tempClause.stream().mapToLong(i -> i).toArray());
        numClauses++;
    }
    @Override
    public void addClause(ArrayList<Long> literals){
        if(CmdFlags.getMaxsattrans()) {
            literals.add(0, top);
        }
        literals.remove(-trueVar);
        iSolver.addClauseToISATSolver(literals.stream().mapToLong(i -> i).toArray());
        numClauses++;
    }
    @Override
    public void addClauseReified(ArrayList<Long> literals, long auxVar) {
        // auxVar -> literals
        ArrayList<Long> t1 = new ArrayList<Long>(literals);
        t1.add(0, -auxVar);
        addClause(t1);
        // For each literal, literal -> auxVar.
        for(int i=0; i<literals.size(); i++) {
            t1.clear();
            t1.add(-literals.get(i));
            t1.add(auxVar);
            addClause(t1);
        }
    }
    @Override
    public void addSoftClause(long lit1, long weight){
        iSolver.addClauseToISATSolver(new long[]{weight, lit1});
        numClauses++;
    }
    @Override
    public void addClauseAfterFinalise(long lit1, boolean removable){
        // Do the same thing as adding a clause if its not removable
        if (removable){
            iSolver.addToAssumptionQueue(lit1);
        }
        else {
            addClause(lit1);
        }
    }

    @Override
    public void addClauseAfterFinalise2(long lit1, long lit2, boolean removable){
        // Do the same thing as adding a clause if its not removable
        if (removable){
            iSolver.addToAssumptionQueue(lit1);
            iSolver.addToAssumptionQueue(lit2);
        }
        else {
            addClause(lit1);
            addClause(lit2);
        }
    }

    @Override
    public void addClauseAfterFinalise(ArrayList<Long> literals){
        // Do the same thing as adding a clause. We don't need to care about file opening
        // In optimisation problems, this can go to adding an assumption instead.
        addClause(literals);
    }

    @Override
    public void removeFinalClause(){
        // This is a dangerous override. But if we make sure last clause is added as removable,
        // the solver handling backend will remove the assumption after the solving stage.
    }
}