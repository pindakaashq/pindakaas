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
import java.util.Arrays;
import java.util.stream.Collectors;

import savilerow.Pair;
import savilerow.expression.Solution;
import savilerow.model.Model;

//  Subclasses of SATSolver provide the runSatSolver method that returns a string
//  containing the solution literals and a stats object.

public class InteractiveAllMinisatSATSolver extends InteractiveSATSolver
{
    public InteractiveAllMinisatSATSolver(Model _m) {
        super(_m);
    }

    @Override
    public Pair<ArrayList<String>, Stats> runSatSolver(String satSolverName, String filename, Model m, Stats statssofar){
        // give assumptions in the beginning
        finaliseAssumptions();
        addAssumptionsToSolver(nativeSolverPointer, Arrays.stream(assumptions).mapToInt(i -> (int)i).toArray());
        double solverTime = System.currentTimeMillis();
        runSolver(nativeSolverPointer, this);
        solverTime = (System.currentTimeMillis() - solverTime) / 1000;
        double[] statsArray = getSolverStats(nativeSolverPointer);
        statsArray[1] = solverTime;
        InteractiveStats stats = new InteractiveAllMinisatStats(statsArray);
        stats.setNbLearnts(getNbLearntClausesFromISATSolver());
        writeToFileSolutionStats(stats);
        return null;
    }

    @Override
    public void findOneSolution(String satSolverName, String fileName, Model m){
        setNbSolutions(nativeSolverPointer, 1);
        runSatSolver(satSolverName, fileName, m, null);
        cleanAssumptionQueue();
    }

    @Override
    public void findMultipleSolutions(String satSolverName, String fileName, Model m) {
        runSatSolver(satSolverName, fileName, m, null);
        cleanAssumptionQueue();
    }

    // Implementation of INativeSolver and JNI Business
    private long nativeSolverPointer;

    private static native long initSolver();
    private static native long addClauseToSolver(long solver, int[] clause);
    private static native long setNbSolutions(long solver, long k);
    private static native long addAssumptionsToSolver(long solver, int[] assumptions);
    private static native long runSolver(long solver, InteractiveSATSolver callbackPointer);
    private static native double[] getSolverStats(long solver);
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
        ArrayList<String> currentSolution = Arrays.stream(solution).mapToObj(Integer::toString).collect(Collectors.toCollection(ArrayList::new));
        Solution sol = solverSolToAST(currentSolution, m.global_symbols);
        createSolutionFile(sol, true);
        // Garbage collector can clean it maybe, so just in case return this object to rust namespace.
        // return solution;
    }

}
