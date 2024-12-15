package savilerow.solver;
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

import java.io.BufferedReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

import savilerow.CmdFlags;
import savilerow.expression.Solution;
import savilerow.model.*;

public class FznSolver extends Solver
{
    private Stats stats=null;
    // solvername is the name of the solver -- e.g. fzn-gecode, fzn-chuffed
    // filename is the name of the minion input file. 
    // m is the model 
    public void findSolutions(String solvername, String filename, Model m) throws IOException,  InterruptedException
    {
        runFznSolver(solvername, filename, m);
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Private methods. 
    
    private void runFznSolver(String solvername, String filename, Model m) throws IOException,  InterruptedException
    {
        CmdFlags.runningSolver=true;  // Prevents SR's timeout from kicking in. 
        
        try
        {
            ArrayList<String> command = new ArrayList<String>();
            command.add(solvername);
            
            if(CmdFlags.getFindAllSolutions()) {
                if(m.objective!=null) {
                    CmdFlags.warning("Ignoring -all-solutions flag because it cannot be used with optimisation.");
                    CmdFlags.setFindAllSolutions(false);
                }
                else {
                    command.add("-n");
                    command.add("0");   // Set number of solutions to 0 -- means find all. 
                }
            }
            
            if(CmdFlags.getFindNumSolutions()>1) {
                if(m.objective!=null) {
                    CmdFlags.warning("Ignoring -num-solutions flag because it cannot be used with optimisation.");
                    CmdFlags.setFindNumSolutions(1);
                }
                else {
                    command.add("-n");
                    command.add(String.valueOf(CmdFlags.getFindNumSolutions()));
                }
            }
            
            if((CmdFlags.getGecodetrans() || CmdFlags.getChuffedtrans() || CmdFlags.getOrtoolstrans()) && !CmdFlags.getSolverExtraFlags().contains("-s")) {
                //  Get some additional stats. 
                CmdFlags.addSolverFlag("-s");
            }
            
            command.addAll(CmdFlags.getSolverExtraFlags());
            
            command.add(filename);
            
            if(CmdFlags.getChuffedtrans() || CmdFlags.getOrtoolstrans()) {
                command.add("-f");   //  Free search
            }
            
            double srtime=(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000);
            
            stats = new Stats();
            stats.putValue("SavileRowTotalTime", String.valueOf(srtime));
            
            if(CmdFlags.getChuffedtrans() || CmdFlags.getGecodetrans() || CmdFlags.getOrtoolstrans()) {
                stats.putValue("SolverTimeOut", "0");  // Default, unless solver reports timeout.
                if(CmdFlags.getGecodetrans() || CmdFlags.getChuffedtrans()) {
                    //  OR-Tools does not report nodes. 
                    stats.putValue("SolverNodes", "0");  //  Default value: sometimes Chuffed does not report nodes.
                }
                stats.putValue("SolverFailures", "0");  // Default in case not reported. 
            }
            
            ArrayList<String> stderr_lines=new ArrayList<String>();
            
            ReadFznOutput rgo=new ReadFznOutput(this, m.global_symbols);
            
            double solvertime=System.currentTimeMillis();
            
            int exitValue=RunCommand.runCommand(true, command, stderr_lines, rgo);
            
            solvertime=(((double) System.currentTimeMillis() - solvertime) / 1000);
            
            if(!stats.hasValue("SolverTotalTime")) {
                stats.putValue("SolverTotalTime", String.valueOf(solvertime));
            }
            
            if(stderr_lines.size()!=0 || exitValue!=0) {
                CmdFlags.println("Solver exited with error code:"+exitValue+" and message:");
                CmdFlags.println(stderr_lines);
                CmdFlags.rmTempFiles();
            }
            stats.makeInfoFiles();
        }
        catch(IOException e1) {
            System.err.println("IOException");
            e1.printStackTrace();
            CmdFlags.rmTempFiles();
            throw e1;
        }
        catch(InterruptedException e2) {
            System.out.println("InterruptedException.");
            CmdFlags.rmTempFiles();
            throw e2;
        }
    }
    
    // Override Solver's method for parsing all solutions.
    @Override
    void parseAllSolverSolutions(SymbolTable st, BufferedReader in) {
        parseFznSolverOut(st, in, true);
    }
    
    // Dummy method
    Solution parseOneSolverSolution(SymbolTable st, BufferedReader in) {
        return null;
    }
    
    Solution parseLastSolverSolution(SymbolTable st, BufferedReader in) {
        return parseFznSolverOut(st, in, false);
    }
    
    Solution parseFznSolverOut(SymbolTable st, BufferedReader in, boolean allSols) {
        ArrayList<String> solversol=null;
        String s=null;  // current line. 
        
        while(true) {
            try {
                s=in.readLine();
            }
            catch(IOException e) {
                s=null;
            }
            
            if(s==null) {
                // Reached the end of the stream or something went wrong reading output. 
                // get out of the while loop. 
                break;
            }
            
            s=s.trim();
            
            if(s.equals("Top level failure!")) {
                // Hack to work around Chuffed
                continue;
            }
            if(s.startsWith("%%%mzn-stat:")) {
                readSolverStats(s);
                continue;
            }
            if(s.contains("Time limit exceeded!"))
            {
                stats.putValue("SolverTimeOut", "1");
            }
            if(s.startsWith("%") || s.equals("")) {
                // Skip other comments.
                continue;
            }
            
            if(s.equals("=====UNSATISFIABLE=====")) {
                // No solutions -- just continue, and report as UNSAT
                stats.putValue("SolverSatisfiable", "0");
                continue;
            }
            
            if(s.equals("==========")) {
                // No further solution -- continue to read stats output. 
                continue;
            }
            
            if(s.equals("=====UNKNOWN=====")) {
                // Could there be other explanations of this output, other than timeout?
                stats.putValue("SolverTimeOut", "1");
                // Continue loop to read stats output.
                continue;
            }
            
            ArrayList<String> solversol1=new ArrayList<String>();
            
            while(! (s.equals("----------") )) {
                solversol1.add(s);
                try {
                    s=in.readLine();
                    s=s.trim();
                }
                catch(IOException e) {
                    s=null;
                }
                if(s==null) {
                    break;
                }
            }
            if(allSols) {
                stats.putValue("SolverSatisfiable", "1");
                Solution sol=solverSolToAST(solversol1, st);
                createSolutionFile(sol, true);
            }
            else {
                solversol=solversol1;
            }
        }
        
        if(allSols) {
            return null;
        }
        
        if(solversol!=null) {
            stats.putValue("SolverSatisfiable", "1");
            Solution sol=solverSolToAST(solversol, st);
            return sol;
        }
        else {
            stats.putValue("SolverSatisfiable", "0");
            return null;
        }
    }
    
    // takes stats lines read by one of the main loops and checks for named
    // statistics from those. 
    private void readSolverStats(String s) {
        if(s.startsWith("%%%mzn-stat: nodes")) {
            stats.putValue("SolverNodes", s.split("=")[1]);
        }
        else if(s.startsWith("%%%mzn-stat: time")) {
            stats.putValue("SolverTotalTime", s.split("=")[1]);
        }
        else if(s.startsWith("%%%mzn-stat: failures")) {
            stats.putValue("SolverFailures", s.split("=")[1]);
        }
    }
    
    // Takes a solution printed out by a Flatzinc solver
    // and turns it into a hashmap mapping variable name to value.
    HashMap<String, Long> readAllAssignments(ArrayList<String> gecodesol, SymbolTable st) {
        HashMap<String, Long> collect_all_values=new HashMap<String, Long>();
        
        // Each string contains an assignment
        //  var = <num>;
        
        for(int i=0; i<gecodesol.size(); i++) {
            String assign=gecodesol.get(i);
            if(!assign.isEmpty()) {   //  Skip empty lines.
                String[] sp=assign.split(" = ");
                //  Check we have two substrings.
                if(sp.length==2) {
                    String[] num=sp[1].split(";");  // chop off the ; and newline
                    
                    String toparse=num[0].trim();
                    if(toparse.equals("true")) {
                        collect_all_values.put(sp[0], 1L);
                    }
                    else if(toparse.equals("false")) {
                        collect_all_values.put(sp[0], 0L);
                    }
                    else {
                        collect_all_values.put(sp[0], Long.parseLong(toparse));
                    }
                }
            }
        }
        
        return collect_all_values;
    }
    
    
    // Thread to read the standard out of gecode and directly parse it, create solution files etc.
    class ReadFznOutput extends ReadProcessOutput {
        ReadFznOutput(FznSolver _fs, SymbolTable _st) {
            fs=_fs;
            st=_st;
        }
        
        BufferedReader br;
        FznSolver fs;
        SymbolTable st;
        
        public void giveInputStream(BufferedReader _br) {
            br=_br;
        }
        
        public void run() {
            if((!CmdFlags.getFindAllSolutions()) && (CmdFlags.getFindNumSolutions()==-1 || CmdFlags.getFindNumSolutions()==1)) {
                // Find one solution only. Takes the last solution because for optimisation that will be the optimal one. 
                Solution sol = fs.parseLastSolverSolution(st, br);
                if(sol!=null || st.m.incumbentSolution!=null) {
                    fs.createSolutionFile( ((sol!=null)?sol:st.m.incumbentSolution), false);
                }
            }
            else {
                // Multiple solutions. 
                fs.parseAllSolverSolutions(st, br);
            }
        }
    }
}
