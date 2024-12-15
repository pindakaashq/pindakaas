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

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import savilerow.*;
import savilerow.model.*;

public abstract class InteractiveSMTSolver extends SMTSolver {
    
    InteractiveRunCommand irc;

    public BufferedWriter outputStream;

    public InteractiveSMTSolver(Model m) {
        super(m);
        irc = new InteractiveRunCommand(m, getCommand(CmdFlags.getSMTSolverPath(), null));
        outputStream = irc.output;
    }

    @Override
    public Pair<ArrayList<String>, Stats> runSatSolver(String satSolverName, String filename, Model m, Stats statssofar) throws IOException, InterruptedException {
        CmdFlags.runningSolver=true;  // Prevents SR's timeout from kicking in.

        long solvertime=System.nanoTime();

        int exitValue = irc.processCurrentModel();

        ArrayList<String> stderr_lines = new ArrayList<String>();
        ArrayList<String> stdout_lines = irc.stdout_lines;
        solvertime= System.nanoTime() - solvertime;

        Stats stats = new Stats();

        detectErrors(exitValue, stdout_lines, stderr_lines, stats);

        // Remove the statistic lines from the output
        if (!CmdFlags.usingBoolector() && stdout_lines.size() > 0) {
            int i = 0;
            while (!stdout_lines.get(i).contains(")") || !stdout_lines.get(i).contains("(")){
                i++;
            }

            List<String> stats_lines = stdout_lines.subList(0, i);
            stdout_lines = new ArrayList<>(stdout_lines.subList(i, stdout_lines.size()));
            updateStats(stats, stats_lines);
        }
        // dont want to rewrite handle output so add sat/unsat to the beginning
        stdout_lines.add(0, exitValue == 10 ? "sat" : "unsat");
        // on interactive boolector doesn't print model additionally.
            
        //z3 doesn't report time if it resolves an instance quickly enough
        //boolector doesn't support the reporting of stats
        // interactive yices reports total solver time. 
        if (stats.getValue("SolverTotalTime").equals("NA") || CmdFlags.usingYices2()) {
            double dSolverTime = ((double)solvertime)/1000000000;
            stats.putValue("SolverTotalTime", String.valueOf(dSolverTime));
        }
        // Clean the assumptions if we are on optimisation mode - it's required because SR wants to run sat solver without generating solutions.
        if (m.objective != null){
            //clean assumption queue for a possible run later
            cleanActiveAssumptions();
        }

        return new Pair<>(handleOutput(stdout_lines, stats), stats);
    }

    /**
     * No file name is given on this override
     */
    @Override
    protected ArrayList<String> getCommand(String satSolverName, String filename) {
        ArrayList<String> command = new ArrayList<String>();
        command.add(satSolverName);

        ArrayList<String> extraflags=new ArrayList<String>(CmdFlags.getSolverExtraFlags());

        command.addAll(extraflags);

        return command;
    }

    public void cleanActiveAssumptions(){
        // clean active assumptions
        ((InteractiveSMT)m.satModel).activeAssumptions.clear();
    }

    @Override
    public void findOneSolution(String satSolverName, String fileName, Model m) {
        super.findOneSolution(satSolverName, fileName, m);
        //clean assumption queue for a possible run later
        cleanActiveAssumptions();
    }

    @Override
    public void findMultipleSolutions(String satSolverName, String fileName, Model m) {
        super.findMultipleSolutions(satSolverName, fileName, m);
        //clean assumption queue for a possible run later
        cleanActiveAssumptions();
    }

}
