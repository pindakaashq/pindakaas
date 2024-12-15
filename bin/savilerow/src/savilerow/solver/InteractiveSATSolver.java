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

import java.util.ArrayList;

import savilerow.model.Model;

public abstract class InteractiveSATSolver extends SATSolver {

    protected ArrayList<Long> assumptionQueue;
    
    protected long[] assumptions;

    public InteractiveSATSolver(Model _m) {
        super(_m);
        initISATSolver();
        assumptions = null;
        assumptionQueue = new ArrayList<Long>();
    }

    protected abstract void initISATSolver();
    public abstract void setRndSeedToISATSolver(long seed);
    public abstract void addClauseToISATSolver(long[] clause);
    protected abstract void handleFreshSolution(int[] solution);
    public abstract long getNbLearntClausesFromISATSolver();

    public void cleanAssumptionQueue(){
        assumptionQueue.clear();
    }

    public void addToAssumptionQueue(long lit){
        assumptionQueue.add(lit);
    }
    
    protected void finaliseAssumptions(){
        assumptions = assumptionQueue.stream().mapToLong(i -> i).toArray();
    }

    @Override
    public void findOneSolution(String satSolverName, String fileName, Model m) {
        super.findOneSolution(satSolverName, fileName, m);
        //clean assumption queue for a possible run later
        cleanAssumptionQueue();
    }

    @Override
    public void findMultipleSolutions(String satSolverName, String fileName, Model m) {
        super.findMultipleSolutions(satSolverName, fileName, m);
        //clean assumption queue for a possible run later
        cleanAssumptionQueue();
    }

}