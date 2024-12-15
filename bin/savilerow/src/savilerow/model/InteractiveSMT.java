package savilerow.model;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Gökberk Koçak and Peter Nightingale
    
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
import java.util.HashSet;

import savilerow.CmdFlags;
import savilerow.solver.*;

public class InteractiveSMT extends SMT {

    private InteractiveSMTSolver iSolver;

    private long assumptionCount;

    // These are the active assumptions. Should be cleared after each solver run.
    public HashSet<String> activeAssumptions;

    public InteractiveSMT(Model m) {
        super(m.global_symbols);
        initInteractiveSolver(m);
        outstream = iSolver.outputStream;
        assumptionCount = 0;
        activeAssumptions = new HashSet<String>();
        try {
            createHeader();
            trueVar=getNextVariableNumber();
            addClause(trueVar);
        } catch (IOException e) {
            CmdFlags.errorExit("Failed to pipe into SMT solver");
        }
    }

    private void initInteractiveSolver(Model m) {
        if (CmdFlags.usingZ3()) {
            CmdFlags.addSolverFlag("-in");
            iSolver = new InteractiveZ3Solver(m);
        } else if (CmdFlags.usingBoolector()) {
            CmdFlags.addSolverFlag("-i");
            iSolver = new InteractiveBoolectorSolver(m);
        } else {
            assert CmdFlags.usingYices2();
            CmdFlags.addSolverFlag("--incremental");
            iSolver = new InteractiveYicesSolver(m);
        }
    }

    public InteractiveSMTSolver getInteractiveSolver() {
        return iSolver;
    }

    @Override
    public void removeFinalClause() {
        // Same as SAT, this is an empty override because we cannot erase hardcoded
        // clauses we have written.
    }

    @Override
    public void removeSolvingInstructions() {
        // Override this as well
    }

    @Override
    public void addClauseAfterFinalise(ArrayList<Long> clause) throws IOException {
        super.addClause(clause);
    }

    @Override
    public void addClauseAfterFinalise(long lit1, boolean removable) throws IOException {
        if (removable) {
            addAssumption(lit1);
        } else {
            super.addClauseAfterFinalise(lit1, false);
        }
    }

    @Override
    public void addClauseAfterFinalise2(long c1, long c2, boolean removable) throws IOException {
        if (removable) {
            addAssumption(c1);
            addAssumption(c2);
        } else {
            super.addClauseAfterFinalise2(c1, c2, false);
        }
    }

    @Override
    public void addSMTClauseAfterFinalise(String clause, boolean removable) throws IOException {
        if (removable) {
            addSMTAssumption(clause);
        } else {
            addSMTClause(clause);
        }
    }

    @Override
    public void addSMTClauseAfterFinalise2(String c1, String c2, boolean removable) throws IOException {
        if (removable) {
            addSMTAssumption(c1);
            addSMTAssumption(c2);
        } else {
            addSMTClause(c1);
            addSMTClause(c2);
        }
    }

    @Override
    public void finaliseOutput() throws IOException {

    }

    /**
     * Returns the name of the last variable.
     */
    public void requestVariableStream() throws IOException {

        // Add the command to get the statistics
        // Not supported by boolector
        if (!CmdFlags.usingBoolector()) {
            outstream.write("(get-info :all-statistics)");
            outstream.newLine();
        }
        
        for (String var : variables) {
            outstream.write("(get-value (" + var + "))");
            outstream.newLine();
        }

        outstream.flush();

    }

    /**
     * This is for looking into the output stream to determine if solver finished writing
     */
    public String getLastVarPrefix(){
        return "((" + variables.get(variables.size() - 1) + " ";
    }

    public void addAssumption(long lit1) throws IOException {
        String assumptionName = "sr_assumption_" + assumptionCount;
        outstream.write("(declare-const " + assumptionName + " Bool)");
        outstream.newLine();

        outstream.write("(assert (= " + assumptionName + " ");
        if(lit1!=-trueVar) {
            writeLiteral(lit1);
        }
        else { 
            outstream.write("false");
        }
        outstream.write("))");
        outstream.newLine();

        activeAssumptions.add(assumptionName);
        numClauses++;
        assumptionCount++;
    }

    public void addSMTAssumption(String clause) throws IOException {
        String assumptionName = "sr_assumption_" + assumptionCount;
        outstream.write("(declare-const " + assumptionName + " Bool)");
        outstream.newLine();

        if (clause == null) {
            outstream.close();
            System.exit(0);
        }
        assert checkParenthesis(clause);

        outstream.write("(assert (= " + assumptionName + " ");
        outstream.write(clause);
        outstream.write("))");
        outstream.newLine();

        activeAssumptions.add(assumptionName);
        numClauses++;
        assumptionCount++;

    }
}
