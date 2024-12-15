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

public class AllMinisatStats extends Stats
{
    public AllMinisatStats(ArrayList<String> stdout_lines) {
        // Pull out # decisions and CPU time.
        //
        for(int i=0; i<stdout_lines.size(); i++) {
            String[] tmp=stdout_lines.get(i).trim().split(":");
            if(tmp[0].startsWith("decisions")) {
                putValue("SolverNodes", tmp[1].split("\\(")[0].trim());
            }
            if(tmp[0].startsWith("CPU time")) {
                putValue("SolverTotalTime", tmp[1].split("sec")[0].trim());
            }
        }

        // For very large problems, it outputs 'INDETERMINATE' without times or decisions
        // Assume this means out of memory.

        if(getValue("SolverNodes").equals("NA") && getValue("SolverTotalTime").equals("NA") && getValue("SolverTimeOut").equals("1")) {
            putValue("SolverNodes", "0");
            putValue("SolverTotalTime", "0");
            putValue("SolverMemOut", "1");
            putValue("SolverTimeOut", "0");
        }
    }

    public void setNontrivialStats(long solutionCount){
      putValue("SolverTimeOut", "0");
      putValue("SolverMemOut", "0");
      if (solutionCount == 0){
        putValue("SolverSatisfiable", "0");
      }
      else{
        putValue("SolverSatisfiable", "1");
      }
      putValue("SolverSolutionsFound", String.valueOf(solutionCount));
    }
    
    public void setTrivialStats(){
      putValue("SolverTimeOut", "0");
      putValue("SolverMemOut", "0");
      putValue("SolverSatisfiable", "0");
      putValue("SolverSolutionsFound", "0");
    }
}
