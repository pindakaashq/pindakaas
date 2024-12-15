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

public class InteractiveAllMinisatStats extends InteractiveStats
{
    public InteractiveAllMinisatStats(double[] statsArray){
    //   v.push(nb);
    //   v.push(time);
    //   v.push(conflicts);
    //   v.push(decisions);
    //   v.push(propagations);
    //   v.push(inspects);
    //   v.push(conflict_literals);
    //   v.push(last_random_seed);
        putValue("SolverSolutionsFound",   String.valueOf(statsArray[0]));
        putValue("SolverTotalTime",        String.valueOf(statsArray[1]));
        putValue("SolverConflicts",        String.valueOf(statsArray[2]));
        putValue("SolverNodes",            String.valueOf(statsArray[3]));
        putValue("SolverPropagations",     String.valueOf(statsArray[4]));
        putValue("SolverInspections",      String.valueOf(statsArray[5]));
        putValue("SolverConflictLiterals", String.valueOf(statsArray[6]));
        putValue("SolverLastRandomSeed",   String.valueOf(statsArray[7]));
    }
}
