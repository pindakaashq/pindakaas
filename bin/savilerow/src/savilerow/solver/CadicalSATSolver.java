package savilerow.solver;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Patrick Spracklen, Peter Nightingale and Gökberk Koçak
    
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

import savilerow.*;
import savilerow.model.Model;

//  Subclasses of SATSolver provide the runSatSolver method that returns a string
//  containing the solution literals and a stats object. 

public class CadicalSATSolver extends SATSolver
{
    public CadicalSATSolver(Model _m) {
        super(_m);
    }

    public Pair<ArrayList<String>, Stats> runSatSolver(String satSolverName, String filename, Model m, Stats statssofar) throws IOException,  InterruptedException
    {
        CmdFlags.runningSolver=true;  // Prevents SR's timeout from kicking in. 
        boolean kis=CmdFlags.getSatFamily().equals("kissat");
        
        try
        {
            ArrayList<String> command = new ArrayList<String>();
            command.add(satSolverName);
            
            ArrayList<String> extraflags=new ArrayList<String>(CmdFlags.getSolverExtraFlags());
            if(statssofar!=null) {
                int tlimit=parseTimeLimit(extraflags, kis);  //  If there is a -t timelimit flag, adjust it. 
                if(tlimit!=-1) {
                    int tlimit2=tlimit-((int)Math.floor(Double.valueOf(statssofar.getValue("SolverTotalTime"))))+1;  // Add some seconds for safety.
                    if(tlimit2>tlimit) {
                        //  Don't let the calculated time limit become larger than the original.
                        tlimit2=tlimit;
                    }
                    if(tlimit2<1) {
                        tlimit2=1;    //  Avoid negative or 0 time limit values.
                    }
                    setTimeLimit(extraflags, kis, tlimit2);
                }
            }
            
            command.addAll(extraflags);
            command.add(filename);
            
            ArrayList<String> stderr_lines=new ArrayList<String>();
            ArrayList<String> stdout_lines=new ArrayList<String>();
            
            ReadProcessOutput rpo=new ReadProcessOutput(stdout_lines);

            double solvertime=System.currentTimeMillis();

            int exitValue=RunCommand.runCommand(true, command, stderr_lines, rpo);

            solvertime=(((double) System.currentTimeMillis() - solvertime) / 1000);

            Stats stats=new CadicalStats(stdout_lines);

            if(exitValue==10) {
                // Satisfiable -- for Cadical

                // Find the line beginning "v " in stdout.
                ArrayList<String> fileContents=new ArrayList<String>();

                for(int i=0; i<stdout_lines.size(); i++) {
                    if(stdout_lines.get(i).startsWith("v ")) {
                        // Split on space to get solution literals.
                        String[] tmp=stdout_lines.get(i).trim().split(" ");
                        // Trim off the trailing 0 and starting v.
                        for(int l=1; l<tmp.length; l++) {
                            fileContents.add(tmp[l]);
                        }
                    }
                }

                return new Pair<ArrayList<String>, Stats>(fileContents, stats);
            }
            else if(exitValue==20) {
                // Unsat.
                return new Pair<ArrayList<String>, Stats>(null, stats);
            }
            else if(stderr_lines.size()!=0 || (exitValue!=10 && exitValue!=20)) {
                CmdFlags.println("SAT solver exited with error code:"+exitValue+" and message:");
                CmdFlags.println(stderr_lines);
                
                //  Check for timeout. 
                int tl=parseTimeLimit(extraflags, kis);
                if(tl!=-1) {
                    if(solvertime>((double)tl)) {
                        stats.putValue("SolverTimeOut", "1");
                    }
                }
            }
            return new Pair<ArrayList<String>, Stats>(null, stats);
        }
        catch(IOException e1) {
            System.err.println("IOException");
            e1.printStackTrace();
            CmdFlags.rmTempFiles();
            return new Pair<ArrayList<String>, Stats>(null, null);
        }
        catch(InterruptedException e2) {
            System.out.println("InterruptedException.");
            CmdFlags.rmTempFiles();
            return new Pair<ArrayList<String>, Stats>(null, null);
        }
    }
    
    int parseTimeLimit(ArrayList<String> extraflags, boolean kis) {
        for(int i=0; i<extraflags.size(); i++) {
            if((!kis) && extraflags.get(i).equals("-t")) {
                return Integer.parseInt(extraflags.get(i+1));
            }
            if(kis && extraflags.get(i).contains("--time=")) {
                return Integer.parseInt(extraflags.get(i).split("=")[1]);
            }
        }
        return -1;
    }
    
    void setTimeLimit(ArrayList<String> extraflags, boolean kis, int tl) {
        for(int i=0; i<extraflags.size(); i++) {
            if((!kis) && extraflags.get(i).equals("-t")) {
                extraflags.set(i+1, String.valueOf(tl));
                return;
            }
            if(kis && extraflags.get(i).contains("--time=")) {
                extraflags.set(i, "--time="+tl);
                return;
            }
        }
    }
}
