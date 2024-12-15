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



import java.util.ArrayList;

public class LingelingStats extends Stats
{
    public LingelingStats(ArrayList<String> stdout_lines) {
        // Pull out # decisions and CPU time.
        for(int i=0; i<stdout_lines.size(); i++) {
            
            // Skip solution lines.
            if(stdout_lines.get(i).charAt(0) == 'v') {
                continue;
            }
            
            String[] tmp=stdout_lines.get(i).trim().split(" +");
            
            if(tmp.length>=3 && tmp[2].equals("decisions,")) {
                putValue("SolverNodes", tmp[1]);
            }
            if(tmp.length>=3 && tmp[2].equals("seconds,")) {
                putValue("SolverTotalTime", tmp[1]);
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
            if(tmp[0].equals("s") && tmp[1].equals("UNKNOWN")) {  //  "s UNKNOWN" probably should be the output. However it is "c s UNKNOWN"
                putValue("SolverTimeOut", "1");
                putValue("SolverMemOut", "0");
                putValue("SolverSatisfiable", "0");
            }
            if(tmp.length>=3 && tmp[0].equals("c") && tmp[1].equals("s") && tmp[2].equals("UNKNOWN")) {
                putValue("SolverTimeOut", "1");
                putValue("SolverMemOut", "0");
                putValue("SolverSatisfiable", "0");
            }
        }
        
        // What about very large files that cause the solver to mem out?
    }
}

