package savilerow.solver;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Peter Nightingale and Gökberk Koçak
    
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

public class CadicalStats extends Stats
{
    public CadicalStats(ArrayList<String> stdout_lines) {
        // Pull out # decisions and CPU time.
        for(int i=0; i<stdout_lines.size(); i++) {
            String[] tmp=stdout_lines.get(i).trim().split(" +");
            
            if(tmp.length>=2 && tmp[0].equals("c") && tmp[1].equals("decisions:") ) {
               putValue("SolverNodes", tmp[2]);
            }

            if(tmp.length>=7 && tmp[0].equals("c") &&  tmp[1].equals("total") && tmp[2].equals("process") && tmp[3].equals("time")) {
                putValue("SolverTotalTime", tmp[6]);
            }
            if(tmp.length>=4 && tmp[0].equals("c") && tmp[1].equals("process-time:")) {
                putValue("SolverTotalTime", tmp[tmp.length-2]);
            }
            // Is the problem satisfiable, unsatisfiable or timed out?
            if(tmp[0].equals("s") && tmp[1].equals("SATISFIABLE")) {
                putValue("SolverTimeOut", "0");
                putValue("SolverMemOut", "0");
                putValue("SolverSatisfiable", "1");
            }
            if(tmp[0].equals("s") && tmp[1].equals("UNSATISFIABLE")) {
                putValue("SolverTimeOut", "0");
                putValue("SolverMemOut", "0");
                putValue("SolverSatisfiable", "0");
            }
            if(tmp[0].equals("s") && tmp[1].equals("INDETERMINATE")) {
                putValue("SolverTimeOut", "1");
                putValue("SolverMemOut", "0");
                putValue("SolverSatisfiable", "0");
            }
        }
        
        // decision line is not there if it's a trivial search or timeout
        if(getValue("SolverNodes").equals("NA")){
            putValue("SolverNodes", "0");
        }

        // For very large problems, it outputs 'INDETERMINATE' without times or decisions
        // Assume this means out of memory. 
        
        if(getValue("SolverTotalTime").equals("NA") && getValue("SolverTimeOut").equals("1")) {
            putValue("SolverTotalTime", "0");
            putValue("SolverMemOut", "1");
            putValue("SolverTimeOut", "0");
        }
    }
    public CadicalStats(boolean sat, double[] statsArray){
        putValue("SolverSatisfiable",    sat ? "1" : "0");
        //time, decisions,propagations,conflicts;
        putValue("SolverTotalTime",    String.valueOf(statsArray[0]));
        putValue("SolverNodes",        String.valueOf(statsArray[1]));
        putValue("SolverPropagations", String.valueOf(statsArray[3]));
        putValue("SolverConflicts",    String.valueOf(statsArray[2]));
    }
}

