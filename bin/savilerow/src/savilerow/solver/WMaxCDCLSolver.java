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

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;

import savilerow.*;
import savilerow.model.Model;

//  Subclasses of SATSolver provide the runSatSolver method that returns a string
//  containing the solution literals and a stats object. 

public class WMaxCDCLSolver extends SATSolver
{
    public WMaxCDCLSolver(Model _m) {
        super(_m);
    }
    public Pair<ArrayList<String>, Stats> runSatSolver(String satSolverName, String filename, Model m, Stats statssofar) throws IOException,  InterruptedException
    {
        CmdFlags.runningSolver=true;  // Prevents SR's timeout from kicking in. 
        try {
            ArrayList<String> command = new ArrayList<String>();
            command.add(satSolverName);
            
            ArrayList<String> extraflags=new ArrayList<String>(CmdFlags.getSolverExtraFlags());
            
            assert statssofar==null;  // Runs once. 
            
            command.addAll(extraflags);
            command.add(filename);
            
            ArrayList<String> stderr_lines=new ArrayList<String>();
            ArrayList<String> stdout_lines=new ArrayList<String>();
            
            ReadProcessOutput rpo=new ReadProcessOutput(stdout_lines);

            double solvertime=System.currentTimeMillis();
            
            int exitValue=RunCommand.runCommand(false, command, stderr_lines, rpo);
            
            CmdFlags.println("MaxSAT solver exited with error code:"+exitValue+" and error message:");
            CmdFlags.println(stderr_lines);
            
            solvertime=(((double) System.currentTimeMillis() - solvertime) / 1000);
            
            Stats stats=new WMaxCDCLStats(stdout_lines);
            stats.putValue("SolverTotalTime", String.valueOf(solvertime));

            boolean satisfiable = stats.hasValue("SolverSatisfiable") && (stats.getValue("SolverSatisfiable")=="1");
            if(satisfiable) {
                ArrayList<String> fileContents=new ArrayList<String>();
                for(String ln : stdout_lines) {
                    CmdFlags.printlnIfVerbose(ln);
                    if(ln.startsWith("v")) {
                        // wmaxcdcl gives "v 00101101" instead of wbo "v -1 -2 3 -4
                        // let's fake the literals
                        String[] parts = ln.trim().split(" ");
                        for (int i=0;i<parts[1].length();i++){
                            String pol = parts[1].substring(i,i+1);
                            if (pol.equals("0")) {
                                fileContents.add("-"+String.valueOf(i+1));
                            }
                            else if (pol.equals("1")) {
                                fileContents.add(String.valueOf(i+1));
                            } else {
                                throw new Exception("Could not interpret binary value "+pol);
                            }
                        }
                    }
                }
                
                return new Pair<ArrayList<String>, Stats>(fileContents, stats);
            }
            else {
                // Either unsat or not completed
                return new Pair<ArrayList<String>, Stats>(null, stats);
            }
        }
        catch(Exception e) {
            System.out.println("Exception."+e);
            CmdFlags.rmTempFiles();
            return new Pair<ArrayList<String>, Stats>(null, null);
        }
    }
}
