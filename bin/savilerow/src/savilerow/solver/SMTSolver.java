package savilerow.solver;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Marc Roig, Ewan Davidson, and Peter Nightingale
    
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

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import savilerow.*;
import savilerow.expression.*;
import savilerow.model.*;

public abstract class SMTSolver extends SATSolver {
    public SMTSolver(Model m) {
        super(m);
    }

    // satSolverName is the name of the SAT solver binary
    // filename is the name of the CNF file.
    // m is the model
    @Override
    public void findSolutions(String satSolverName, String fileName, Model m) throws IOException,  InterruptedException
    {
        //If there is an objective (maximising/minimising)
        if (m.objective!=null) {
            if (CmdFlags.getSMTEncodeObjective()) {
                findOneSolution(satSolverName, fileName, m);
            }
            else {
                findObjective(satSolverName,fileName, m);
            }
        }

        //Check if all solutions are required
        else if(CmdFlags.getFindAllSolutions() || CmdFlags.getFindNumSolutions()>1) {
            findMultipleSolutions(satSolverName,fileName,m);
        }
        else {
            findOneSolution(satSolverName, fileName, m);
        }
        CmdFlags.rmTempFiles();
    }

    @Override
    public Pair<ArrayList<String>, Stats> runSatSolver(String satSolverName, String filename, Model m, Stats statssofar) throws IOException, InterruptedException {
        CmdFlags.runningSolver=true;  // Prevents SR's timeout from kicking in.
        
        ArrayList<String> command = getCommand(satSolverName, filename);
        
        ArrayList<String> stderr_lines=new ArrayList<String>();
        ArrayList<String> stdout_lines=new ArrayList<String>();
        
        ReadProcessOutput rpo=new ReadProcessOutput(stdout_lines);

        long solvertime=System.nanoTime();

        int exitValue=RunCommand.runCommand(false, command, stderr_lines, rpo);

        solvertime= System.nanoTime() - solvertime;

        Stats stats = new Stats();

        detectErrors(exitValue, stdout_lines, stderr_lines, stats);

        // Remove the statistic lines from the output
        if (!CmdFlags.usingBoolector()) {

            int i = stdout_lines.size() - 1;
            if (stdout_lines.get(i).contains(")") && !stdout_lines.get(i).contains("("))
                while (i > 0 && !stdout_lines.get(i).contains("("))
                    i--;

            List<String> stats_lines = stdout_lines.subList(i, stdout_lines.size());
            stdout_lines = new ArrayList<>(stdout_lines.subList(0, i));

            updateStats(stats, stats_lines);
        }
        else {
            //Boolector displays the model in addition to the desired
            //variables need to remove model
            int i = stdout_lines.size() - 1;
            while (i > 0 && !stdout_lines.get(i).contains(")")) { i--; }
            stdout_lines = new ArrayList<>(stdout_lines.subList(0,i+1));
        }

        //z3 doesn't report time if it resolves an instance quickly enough
        //boolector doesn't support the reporting of stats
        if (stats.getValue("SolverTotalTime").equals("NA")) {
            double dSolverTime = ((double)solvertime)/1000000000;
            stats.putValue("SolverTotalTime", String.valueOf(dSolverTime));
        }
        return new Pair<>(handleOutput(stdout_lines, stats), stats);
    }

    protected ArrayList<String> getCommand(String satSolverName, String filename) {
        ArrayList<String> command = new ArrayList<String>();
        command.add(satSolverName);

        ArrayList<String> extraflags=new ArrayList<String>(CmdFlags.getSolverExtraFlags());

        command.addAll(extraflags);
        command.add(filename);

        return command;
    }

    // Handles the errors that the different solvers may give
    protected abstract void detectErrors(int exitValue, ArrayList<String> stdout_lines, ArrayList<String> stderr_lines, Stats stats);

    // Parses the stats and keeps the ones
    protected void updateStats(Stats stats, List<String> stats_lines) {
        for (String l : stats_lines) {
            if (l.contains(":")) {
                String line = l.split(":")[1];

                String[] parts = line.split("\\s+");

                String header = getHeader(parts[0]);

                if (header != null)
                    stats.putValue(header, parts[1].replace(")", ""));
            }
        }
    }

    // Returns the SavileRow standard for the statistic name or null if we do not use it
    protected abstract String getHeader(String statistic);
    
    // Parses the output of the used solver for SMT-LIB
    protected ArrayList<String> handleOutput(ArrayList<String> stdout_lines, Stats stats) {
        if(stdout_lines.size()>0 && stdout_lines.get(0).equals("sat")) {
            stats.putValue("SolverSatisfiable", "1");
			return new ArrayList<String>(stdout_lines.subList(1, stdout_lines.size()));
        }
        else if(stdout_lines.size()>0 && stdout_lines.get(0).equals("unsat")) {
			stats.putValue("SolverSatisfiable", "0");
			return null;
        }
        else if(stdout_lines.size()>0 && stdout_lines.get(0).equals("unknown")) {
			stats.putValue("SolverSatisfiable", "0");
			return null;
        }
        else if(stdout_lines.contains("unsat")) {
            stats.putValue("SolverSatisfiable", "0");
			return null;
        }
        else {
        	CmdFlags.warning("SMT solver produced unexpected output. Assuming no solution found.");
        	stats.putValue("SolverSatisfiable", "0");
        	return null;
        }
    }

    // Takes a solution as SAT literals
    // and turns it into a hashmap mapping variable name to value.
    HashMap<String, Long> readAllAssignments(ArrayList<String> satSol, SymbolTable st) {
        HashMap<String, Long> collect_all_values=new HashMap<String, Long>();

        Sat satModel=st.m.satModel;

        long assignprev=0;

        for (String line : satSol) {
            if(line.startsWith("(model") || line.trim().equals("(")) {
                // we are done reading the solution
                break;
            }
            
            String[] aux = line.split(" ", 2);

            String var = aux[0].substring(2);
            String value = aux[1].substring(0, aux[1].length() - 2);

            if (CmdFlags.usingBoolector() && !st.isBitVector(var)) {

                if (value.equals("#b1")) { value = "true"; }
                if (value.equals("#b0")) { value = "false"; }
            }
            
            if(value.equals("true") || value.equals("false")) {
                long assign = Long.valueOf(var.substring(1)); // Get the variable number by removing the x at the start
                
                if (value.contains("false"))
                    assign = -assign;
                
                //  Direct encoding
                NumberMap n = satModel.getDimacsMapping(assign);
                
                if (n != null) {
                    collect_all_values.put(n.getVariable(), n.getValue());
                    assignprev = assign;
                    continue;
                }

                // Order encoding -- for variables that have only order encoding.
                // Solvers MUST output literals in order for this to work.

                // There are three cases. For the first var in the order enc, i.e. [x<=min(D(x))],
                // if the literal is positive we find it in orderMappingMin to get the SR variable and value.

                if (assign > 0) {
                    n = satModel.orderMappingMin.get(assign);
                    if (n != null) {
                        collect_all_values.put(n.getVariable(), n.getValue());
                        assignprev = assign;
                        continue;
                    }
                }

                // For other vars in the order enc, if the var is positive and its
                // predecessor is negative, then we can find it in orderMappingMid.

                if (assign > 0 && assignprev < 0) {
                    n = satModel.orderMappingMid.get(assign);
                    if (n != null) {
                        collect_all_values.put(n.getVariable(), n.getValue());
                        assignprev = assign;
                        continue;
                    }
                }

                // For the top value in the domain, there is no [x<=max(D(x))] SAT variable
                // The topmost SAT variable must be false in this case so we use that.

                if (assign < 0) {
                    n = satModel.orderMappingMax.get(assign);
                    if (n != null) {
                        collect_all_values.put(n.getVariable(), n.getValue());
                        assignprev = assign;
                        continue;
                    }
                }

                assignprev = assign;  // Store for next iteration
            }
            else {
                // If the variable has another type of value (which should be integer)
                value = value.replaceAll("[() ]", "");
                if (CmdFlags.getUseBV()) {
                    collect_all_values.put(var, BitVector.toLong(value));
                }
                else { collect_all_values.put(var, Long.valueOf(value)); }
            }
        }

        // Bit of a hack -- should be somewhere else.
        if(CmdFlags.test_solutions) {
            checkSolution(collect_all_values);
        }

        return collect_all_values;
    }
    
    protected void dichotomicSearch(Identifier objectiveNode, long mid) throws IOException {
        // Add the clause opt<=mid or opt>=mid
        // Construct the new clause.
        if (m.global_symbols.isInteger(m.objective.getChild(0).toString())) {
            if (m.objective instanceof Minimising) {
                ((SMT)m.satModel).addSMTClauseAfterFinalise("(<= " + objectiveNode.getName() + " " + mid + ")", true);
            }
            else {
                ((SMT)m.satModel).addSMTClauseAfterFinalise("(>= " + objectiveNode.getName() + " " + mid + ")", true);
            }
        }
        else if (m.global_symbols.isBitVector(m.objective.getChild(0).toString())) {
            if (m.objective instanceof Minimising) {
                ((SMT)m.satModel).addSMTClauseAfterFinalise("(bvsle " + objectiveNode.getName() + " " + BitVector.toHexString(mid) + ")", true);
            }
            else {
                ((SMT)m.satModel).addSMTClauseAfterFinalise("(bvsge " + objectiveNode.getName() + " " + BitVector.toHexString(mid) + ")", true);
            }
        }
        else {
            super.dichotomicSearch(objectiveNode, mid);
        }
    }

    protected void boundSearch(ASTNode objectiveNode, long upper, long lower) throws IOException {
        //  Permanently bound the search within lower..upper
        if (m.global_symbols.isInteger(objectiveNode.toString())) {
            ((SMT)m.satModel).addSMTClauseAfterFinalise2("(<= " + objectiveNode.toString() + " " + upper + ")",
                "(>= " + objectiveNode.toString() + " " + lower + ")", false);
        }
        else if (m.global_symbols.isBitVector(objectiveNode.toString())) {
            ((SMT)m.satModel).addSMTClauseAfterFinalise2("(bvsle " + objectiveNode.toString() + " " + BitVector.toHexString(upper) + ")",
                "(bvsge " + objectiveNode.toString() + " " + BitVector.toHexString(lower) + ")", false);
        }
        else {
            super.boundSearch(objectiveNode, upper, lower);
        }
    }

    protected void boundSearchRemovable(ASTNode objectiveNode, long upper, long lower) throws IOException {
        //  Temporarily bound the search within lower..upper
        if (m.global_symbols.isInteger(objectiveNode.toString())) {
            ((SMT)m.satModel).addSMTClauseAfterFinalise2("(<= " + objectiveNode.toString() + " " + upper + ")",
                "(>= " + objectiveNode.toString() + " " + lower + ")", true);
        }
        else if (m.global_symbols.isBitVector(objectiveNode.toString())) {
            ((SMT)m.satModel).addSMTClauseAfterFinalise2("(bvsle " + objectiveNode.toString() + " " + BitVector.toHexString(upper) + ")",
                "(bvsge " + objectiveNode.toString() + " " + BitVector.toHexString(lower) + ")", true);
        }
        else {
            super.boundSearchRemovable(objectiveNode, upper, lower);
        }
    }
    
    protected void findObjectiveLinearAddBound(Identifier objectiveNode, long objectiveValue) throws IOException {
        if (m.global_symbols.isInteger(m.objective.getChild(0).toString())) {
            if(m.objective instanceof Minimising) {
                ((SMT)m.satModel).addSMTClauseAfterFinalise("(< " + objectiveNode.getName() + " " + objectiveValue + ")", false);
            }
            else {
                ((SMT)m.satModel).addSMTClauseAfterFinalise("(> " + objectiveNode.getName() + " " + objectiveValue + ")", false);
            }
        }
        else if (m.global_symbols.isBitVector(m.objective.getChild(0).toString())) {
            if(m.objective instanceof Minimising) {
                ((SMT)m.satModel).addSMTClauseAfterFinalise("(bvsle " + objectiveNode.getName() + " " + BitVector.toHexString(objectiveValue-1) + ")", false);
            }
            else {
                ((SMT)m.satModel).addSMTClauseAfterFinalise("(bvsge " + objectiveNode.getName() + " " + BitVector.toHexString(objectiveValue+1) + ")", false);
            }
        }
        else {
            super.findObjectiveLinearAddBound(objectiveNode, objectiveValue);
        }
    }
    
    //  Add a clause to block a solution. 
    @Override
    public void addBlockingClause(ArrayList<ASTNode> vars, ArrayList<Long> vals) throws IOException {
        StringBuilder b=new StringBuilder();
        b.append("(or ");
        
        for(int i=0; i<vars.size(); i++) {
            ASTNode var=vars.get(i);
            long value=vals.get(i);
            if(m.global_symbols.isInteger(var.toString())) {
                b.append("(distinct " + var + " " + value + ") ");
            }
            else if(m.global_symbols.isBitVector(var.toString())) {
                b.append("(not (= " + var + " " + BitVector.toHexString(value) + ")) ");
            }
            else {
                //  Fall back to SAT
                long lit = -var.directEncode(m.satModel, value);
                if(lit==1) {
                    //  There is no direct encoding of this var/val pair. Must be that the variable has no direct encoding. Use the order encoding.
                    //  Either less than or greater than the val.
                    b.append(SMT.toLiteral(var.orderEncode(m.satModel, value-1)));
                    b.append(" ");
                    b.append(SMT.toLiteral(-var.orderEncode(m.satModel, value)));
                    b.append(" ");
                }
                else {
                    b.append(SMT.toLiteral(lit));
                    b.append(" ");
                }
            }
        }
        b.append(")");
        ((SMT)m.satModel).addSMTClauseAfterFinalise(b.toString(), false);
    }
}
