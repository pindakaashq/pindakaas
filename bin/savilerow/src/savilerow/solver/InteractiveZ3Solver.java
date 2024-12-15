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

public class InteractiveZ3Solver extends InteractiveSMTSolver {
    public static final String RUN_TIME = "time";
    public static final String DECISIONS = "decisions";
    public static final String RESTARTS = "restarts";
    public static final String BIN_PROP = "binary-propagations";
    public static final String PROPAGATIONS = "propagations";

    public InteractiveZ3Solver(Model _m) { 
        super(_m);
    }

    protected void detectErrors(int exitValue, ArrayList<String> stdout_lines, ArrayList<String> stderr_lines, Stats stats) {
        if( stderr_lines.size()!=0 || (exitValue!=10 && exitValue != 20)) {
            CmdFlags.println("z3 exited with error code:"+exitValue+" and error message:");
            CmdFlags.println(stderr_lines);
        }

        // if (stdout_lines.size() == 0) {
        //     CmdFlags.errorExit("Output for z3 not found");
        // }
    }

    // Returns the SavileRow standard for the statistic name or null if we do not use it
    protected String getHeader(String statistic) {
        switch (statistic) {
            case RUN_TIME:
                return "SolverTotalTime";
            case DECISIONS:
                return "SolverNodes";
            case RESTARTS:
                return "Restarts";
            case BIN_PROP:
                return "BinaryPropagations";
            case PROPAGATIONS:
                return "Propagations";
            default:
                return null;
        }
    }
}
