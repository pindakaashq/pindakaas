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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.stream.Collectors;

import savilerow.Pair;
import savilerow.model.Model;

//  Subclasses of SATSolver provide the runSatSolver method that returns a string
//  containing the solution literals and a stats object. 

public class InteractiveGlucoseSATSolver extends InteractiveSATSolver
{
    public InteractiveGlucoseSATSolver(Model _m) {
        super(_m);
    }

    @Override
    public Pair<ArrayList<String>, Stats> runSatSolver(String satSolverName, String filename, Model m, Stats statssofar){
        // give assumptions in the beginning
        finaliseAssumptions();
        addAssumptionsToSolver(nativeSolverPointer, Arrays.stream(assumptions).mapToInt(i -> (int)i).toArray());
        double solverTime = System.currentTimeMillis();
        long ret = runSolver(nativeSolverPointer, this, m.satModel.variableNumber-1);
        solverTime = (System.currentTimeMillis() - solverTime) / 1000;
        double[] statsArray = new double[2];
        statsArray[0] = solverTime;
        statsArray[1] = getSolverStats(nativeSolverPointer);
        InteractiveStats stats = new InteractiveGlucoseStats(ret == 0 ? true : false, statsArray);
        stats.setNbLearnts(getNbLearntClausesFromISATSolver());
        // Clean the assumptions if we are on optimisation mode - it's required because SR wants to run sat solver without generating solutions.
        if (m.objective != null){
            //clean assumption queue for a possible run later
            cleanAssumptionQueue();
        }
        return new Pair<ArrayList<String>, Stats>(ret == 0 ? lastSolution : null, stats);
    }

    // Implementation of INativeSolver and JNI Business
    private long nativeSolverPointer;
    // Solver sends to solution immediately to SR and Handle solution captures it possibly many purposes. 
    private ArrayList<String> lastSolution;

    private static native long initSolver();
    private static native long addClauseToSolver(long solver, int[] clause);
    private static native long addAssumptionsToSolver(long solver, int[] assumptions);
    private static native long runSolver(long solver, InteractiveSATSolver callbackPointer, long nbVars);
    private static native long getSolverStats(long solver);
    private static native long setRndSeed(long solver, long seed);
    private static native long getNbLearntClauses(long solver);

    static {
        System.loadLibrary("rust_jni_solvers");
    }

    protected void initISATSolver(){
        nativeSolverPointer = initSolver();
        assert(nativeSolverPointer != 0);
    }

    public void setRndSeedToISATSolver(long seed) {
        setRndSeed(nativeSolverPointer,  seed);
    }

    public void addClauseToISATSolver(long[] clause){
        addClauseToSolver(nativeSolverPointer, Arrays.stream(clause).mapToInt(i -> (int)i).toArray());
    }
    
    public long getNbLearntClausesFromISATSolver(){
        return getNbLearntClauses(nativeSolverPointer);
    }

    protected void handleFreshSolution(int[] solution){
        // set last solution to solution call back.
        lastSolution = Arrays.stream(solution).mapToObj(Integer::toString).collect(Collectors.toCollection(ArrayList::new));
        // Garbage collector can clean it maybe, so just in case return this object to rust namespace.
        // return solution;
    }

}
