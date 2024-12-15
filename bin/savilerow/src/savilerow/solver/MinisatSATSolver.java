package savilerow.solver;
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

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;

import savilerow.*;
import savilerow.model.Model;

//  Subclasses of SATSolver provide the runSatSolver method that returns a string
//  containing the solution literals and a stats object. 

public class MinisatSATSolver extends SATSolver
{
    public MinisatSATSolver(Model _m) {
        super(_m);
    }
    public Pair<ArrayList<String>, Stats> runSatSolver(String satSolverName, String filename, Model m, Stats statssofar) throws IOException,  InterruptedException
    {
        CmdFlags.runningSolver=true;  // Prevents SR's timeout from kicking in. 
        
        try
        {
            ArrayList<String> command = new ArrayList<String>();
            command.add(satSolverName);
            //command.add("-cpu-lim=3600");
            command.addAll(CmdFlags.getSolverExtraFlags());
            command.add(filename);
            command.add(CmdFlags.getMinionSolsTempFile());   // One of the temp files that will be cleaned up when SR exits. 
            
            ArrayList<String> stderr_lines=new ArrayList<String>();
            ArrayList<String> stdout_lines=new ArrayList<String>();
            
            ReadProcessOutput rpo=new ReadProcessOutput(stdout_lines);
            
            double solvertime=System.currentTimeMillis();
            
            int exitValue=RunCommand.runCommand(true, command, stderr_lines, rpo);
            
            solvertime=(((double) System.currentTimeMillis() - solvertime) / 1000);
            
            Stats stats=new MinisatStats(stdout_lines);
            
            if(exitValue==10) {
                // Satisfiable -- for MiniSat
                BufferedReader inFromFile =new BufferedReader(new FileReader(CmdFlags.getMinionSolsTempFile()));
                ArrayList<String> fileContents=new ArrayList<String>();
                
                while (inFromFile.ready())
                {
                    String currentLine=inFromFile.readLine();
                    fileContents.add(currentLine);
                }
                
                // Take only line 1. Split on space to get solution literals. 
                fileContents=new ArrayList<String>(Arrays.asList(fileContents.get(1).trim().split(" ")));
                
                // Trim off the trailing 0.
                fileContents.remove(fileContents.size()-1);
                
                return new Pair<ArrayList<String>, Stats>(fileContents, stats);
            }
            else if(exitValue==20) {
                // Unsat.
                return new Pair<ArrayList<String>, Stats>(null, stats);
            }
            else if(stderr_lines.size()!=0 || (exitValue!=10 && exitValue!=20)) {
                CmdFlags.println("SAT solver exited with error code:"+exitValue+" and message:");
                CmdFlags.println(stderr_lines);    
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
    
}
