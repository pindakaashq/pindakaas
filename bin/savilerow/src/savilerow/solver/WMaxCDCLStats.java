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

public class WMaxCDCLStats extends Stats
{
    public WMaxCDCLStats(ArrayList<String> stdout_lines) {
        // Almost nothing to find. 

        for(String line : stdout_lines) {
            // Skip solution lines.
            if(line.startsWith("v")) {
                continue;
            }
            
            String[] tmp=line.trim().split(" +");
            if(tmp[0].equals("s") && tmp[1].equals("OPTIMUM")) {
                putValue("SolverTimeOut", "0");
                putValue("SolverMemOut", "0");
                putValue("SolverSatisfiable", "1");
            }
            else if(tmp[0].equals("s") && tmp[1].equals("UNSATISFIABLE")) {
                putValue("SolverTimeOut", "0");
                putValue("SolverMemOut", "0");
                putValue("SolverSatisfiable", "0");
            }
            else if(tmp[0].equals("s") && tmp[1].equals("UNKNOWN")) {
                putValue("SolverTimeOut", "1");
                putValue("SolverMemOut", "0");
                putValue("SolverSatisfiable", "0");
            }
        }
    }
}
