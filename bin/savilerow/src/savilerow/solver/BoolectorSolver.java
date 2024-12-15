package savilerow.solver;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Marc Roig, Ewan Davidson
    
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

import savilerow.CmdFlags;
import savilerow.model.Model;

public class BoolectorSolver extends SMTSolver {

    public BoolectorSolver(Model _m) { super(_m); }

    protected void detectErrors(int exitValue, ArrayList<String> stdout_lines, ArrayList<String> stderr_lines, Stats stats) {

        if( stderr_lines.size()!=0 || (exitValue!=0 && exitValue != 1)) {
            StringBuilder builder = new StringBuilder();
            builder.append("boolector exited with error code:"+exitValue+" and error message:");
            builder.append("\n");
            for (int i = 0; i < stderr_lines.size(); i++) {
                builder.append(stderr_lines.get(i));
                builder.append("\n");
            }

            //boolector will return exit code 1 when unsat,
            if (exitValue != 10 && exitValue!= 1) {
                CmdFlags.errorExit(builder.toString());
            }
        }

        if (stdout_lines.size() == 0) {
            CmdFlags.errorExit("Output for boolector not found");
        }
    }

    // Always returns null as boolector doesn't support get-statistic
    protected String getHeader(String statistic) {

        return null;
    }
}