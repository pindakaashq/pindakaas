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

public class YicesSolver extends SMTSolver {
    public static final int YICES_OUT_OF_MEMORY = 16;

    public static final String RUN_TIME = "total-run-time";
    public static final String DECISIONS = "decisions";
    public static final String RESTARTS = "restarts";
    public static final String BOOL_PROP = "boolean-propagations";
    public static final String THEORY_PROP = "theory-propagations";

    public YicesSolver(Model m) { super(m); }

    @Override
    protected void detectErrors(int exitValue, ArrayList<String> stdout_lines, ArrayList<String> stderr_lines, Stats stats) {
        // By default, we assume we didn't run out of memeory
        stats.putValue("SolverMemOut", "0");

        if( stderr_lines.size()!=0 || (exitValue!=0 && exitValue != 1)) {
            CmdFlags.println("yices exited with error code:"+exitValue+" and error message:");
            CmdFlags.println(stderr_lines);

            if (exitValue == YICES_OUT_OF_MEMORY) {
                stats.putValue("SolverMemOut", "1");
                CmdFlags.typeError("yices ran out of memory");
            }
        }
        else
            // If we do not have an error it is because it has not timed out
            stats.putValue("SolverTimeOut", "0");

        if (stdout_lines.size() == 0) {
            CmdFlags.errorExit("Output for yices not found");
        }
        else if (stdout_lines.get(0).startsWith("(error")) {
            CmdFlags.errorExit("Solver exited with error: " + stdout_lines.get(0));
        }
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
            case BOOL_PROP:
                return "BoolPropagations";
            case THEORY_PROP:
                return "TheoryPropagations";
            default:
                return null;
        }
    }
}
