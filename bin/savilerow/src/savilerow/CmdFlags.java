package savilerow;
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

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Random;

import savilerow.model.Model;

public final class CmdFlags {
    public enum LOGIC {QF_UF, QF_IDL, QF_LIA, QF_NIA, QF_BV, NULL}
    public enum ENCODING {FLAT, NESTED, NULL}
    public enum SMTSOL {DEFAULT, BOOLECTOR, Z3, YICES2}
    
    private static boolean verbose = false;
    
    private static String minionpath = "minion";
    private static String gecodepath = "fzn-gecode";
    private static String chuffedpath = "fzn-chuffed";
    private static String ortoolspath = "fzn-cp-sat";
    private static String fznpath = null;
    private static String symdetectpath="symmetry_detect";
    
    //  SMT
    private static String boolectorpath=null;
    private static String z3path=null;
    private static String yicespath=null;
    private static SMTSOL smtsolver=SMTSOL.DEFAULT;
    private static String smtsolverpath=null;
    public static String smtseed="1";
    // SMT logic
    private static LOGIC logic = LOGIC.NULL;
    // SMT encoding
    private static ENCODING encoding = ENCODING.NULL;
    // Allow auxiliary SMT variables
    private static boolean aux_smt = false;
    
    private static boolean smt_decomp_alldiff = true;
    private static boolean smt_pairwise_alldiff = false;  // Use linear decomposition by default.
    
    //  SAT  &  MaxSAT
    private static String maxsatpath="wmaxcdcl";
    private static String satsolverpath = null;   // Set a default value based on sat family and maxsat/not maxsat.
    private static String kissatpath = null;     // Stored separately so that the bundled one can be supplied on the command-line.
    private static String satfamily = null;       // Type of SAT solver for parsing output.
    
    public static boolean satoutputmapping=false;     // Output extended details about how variables are encoded
    
    private static boolean runsolver=false;
    
    public static SolEnum soltype = SolEnum.DEFAULT;
    
    private static boolean use_cse=true;
    private static boolean use_ac_cse=false;
    private static boolean use_active_ac_cse=false;
    private static boolean use_active_ac_cse2=false;
    private static boolean use_active_cse=true;    // Default is -O2 with active CSE on.
    private static boolean use_ac_cse_alt=false;
    
    ////////////////////////////////////////////////////////////////////////////
    //  SAT encoding options
    
    public static boolean use_polarity=false;
    
    public static SumEnc pb_encoding=SumEnc.DEFAULT;   //  Encoding of PB constraints
    public static SumEnc sum_encoding=SumEnc.DEFAULT;  //  Encoding of non-PB sum constraints
    
    public static boolean amo_detect=false;
    public static boolean amo_detect_override=false;
    public static boolean amo_detect_strong=false;
    
    public static AMOEnc sat_amo_encoding=AMOEnc.DEFAULT;   //  Encoding of AMO and EO constraints
    public static boolean rggt_mutex=false;  // Use mutexes between cliques in RGGT encoding.
    public static boolean rggt_stats=false;
    public static boolean rggt_reduce=false;  // Reduce number of clauses with RGGT. 
    public static int bimander_g=2; //  Group size for bimander AMO encoding. 
    
    public static boolean sat_table_mdd=false;
    public static boolean sat_matrixderef_decomp=false;
    public static boolean sat_element_gac=false;
    
    public static boolean short_tab_sat_extra=false;   // Extra clauses in short table encoding to make the aux SAT variables functional.
    //  End SAT encoding options. 
    
    public static ArrayList<Integer> make_tables_scope;
    public static boolean make_tab=false;      // Generate all pairs/triples/etc to tabulate. 
    public static int make_tab_scope=0;        // Number of variables in scope. 
    
    public static boolean verbose_make_short=false; // Should we print extra information when making short tables
    public static int table_squash=0; // How should we try to squash tables?
    //   0 : Not at all
    //   1 : Squash Short -> Short
    //   2 : Squash Long -> Short
    //   3 : Squash both Long and Short
    
    public static int make_short_tab=2;    //  What to do with makeTable function
    //   0 is throw away makeTable function,
    //   1 is make a conventional table constraint
    //   2 make a tableshort constraint. 
    //   3 Apply heuristics to decide, for boolean expressions, whether to tabulate (make a full-length table). Exactly as described in CP'18 paper. 
    //   4 is same as 3 but make a tableshort. 
    public static boolean tabulate_opt=false;
    public static boolean tabulate2=false;
    public static boolean tabulate_diagnostics=false;
    public static boolean tabulate_nolimit=false;    ///   Remove the usual 300000 node limit. 
    
    public static double tabtime=-1.0;
    
    // Optimisations that may change number of solutions.
    private static boolean use_var_symmetry_breaking=false;
    //  Graph colouring specific symmetry breaking. Should be generalised in time.
    private static boolean graph_col_sym_break=false;
    
    public static int accse_heuristic=1;   // Default is most occurrences first. 
    
    // Do dry runs to warm up the JVM
    public static boolean dryruns=false;
    
    // Extra presolving of model. 
    private static boolean use_delete_vars=true;   // Delete variables by unifying or assigning. Default is -O2 with this switched on. 
    private static boolean use_propagate=true;     // Reduce domains by running Minion with SACBounds. On by default.
    private static boolean use_propagate_extend=false;   // Extended propagate- filters aux vars as well as find vars. 
    private static boolean use_propagate_extend2=false;  // ... and tightens getBounds (in addition to above). 
    
    private static boolean remove_redundant_vars=false;  // remove redundant variables or not.
                                                         // Note: setting it to true will lose solutions.
                                                         // false by default
    private static boolean aux_non_functional=false;     //  Allow auxiliary variables that are not functional on the primary variables 
                                                         //  (or transitively functional through other auxs)
    
    private static boolean opt_warm_start=false;         //  For non-Minion output when optimising, run Minion with a small node limit to 
                                                         //  find an easy solution to bound the optimisation variable. 
    private static String opt_strategy="bisect";         //  "linear" has an incumbent solution and gradually improves it 
                                                         //  "unsat" assigns the opt var from the best value up/downwards so the first solution is optimal
                                                         //  "bisect" is dichotomic search. 
    
    private static long find_num_solutions=1;            //  Find 1 solution by default.
    private static boolean solutions_to_stdout_one_line=false;
    private static boolean solutions_to_stdout=false;
    private static boolean solutions_to_null=false;
    private static boolean keep_dimacs_file=false;
    public static boolean output_all_sols=false;  //  Output intermediate solutions when optimising. 
    
    private static boolean use_boundvars=true;
    
    private static boolean use_aggregate=true;  // Default -O2 with aggregation on.
    
    public static boolean test_solutions=false; // Store the model and check the solver solution satisfies all constraints. 
    
    public static boolean param_to_json=false;  // Just dump the parameter file to JSON.
    
    private static boolean expand_short_tab=false;
    
    private static boolean warn_undef=false;
    
    private static boolean save_symbols=false;  //  Save the symbol table to allow translating solutions back. 
    
    public static boolean element_gac=false;
    
    public static boolean factor_encoding=false;  // Apply the factor encoding to table constraints. 
    public static int factor_encoding_mode=1;     //  1 = FE, 2= FDE, 3=FDE++
    
    //  Flags controlling the simplify methods. 
    
    private static boolean output_ready=false;
    private static boolean after_aggregate=false;
    
    // Modes of operation. 
    public static final int Normal=1;         // Produce an output file, plus optionally run Minion and parse the solution(s). 
    public static final int ReadSolution=2;   // Use a stored representation of the symbol table to parse a solution file.
    public static final int ReadDomainStore=3;    // Read a set of domains and translate back to EPrime for visualisation.
    
    //  DominanceRelation problems involving multiple calls and SAT. 
    public static boolean dominanceRelation=false;
    public static boolean compressDominance = false;
    public static boolean interactiveSolver = false;
    public static boolean noblockDom = false;
    public static String dom_flatten_strategy = "full";

    private static int seed = 1234;
    private static Random randomGen = null;
    
    private static int mode=Normal;
    
    public static String version="1.10.1";
    
    public static ArrayList<String> solverflags;
    
    private static String tempFileSuffix = "_" + System.currentTimeMillis()
                                         + "_" + getPid();
    private static String minionStatsTempFile = ".MINIONSTATS" + tempFileSuffix;
    private static String minionSolsTempFile  = ".MINIONSOLS" + tempFileSuffix;
    
    public static volatile long startTime = System.currentTimeMillis();
    public static String preprocess=null;
    public static String eprimefile=null;
    public static String paramfile=null;
    public static String paramstring=null;   //   Parameter file provided on cmd line. 
    public static String solutionfile=null;
    public static String minionsolfile=null;
    public static String infofile=null;
    public static String minionfile=null;
    public static String fznfile=null;
    public static String minizincfile=null;
    public static String satfile=null;
    public static String smtfile=null;
    public static String mipfile=null;
    public static String auxfile=null;
    public static FileWriter recordIntermediateObjectiveValues=null;        // if not null, record intermediate objective values to file
    public static long timelimit=0;
    public static long cnflimit=0;
    public static volatile boolean runningSolver=false;
    private static boolean bvTraversal=false;

    public static LinkedHashMap<String, Integer> stats=new LinkedHashMap<String, Integer>();
    
    public static Model checkSolModel;  // If checking solutions, this field is used to store the model before any solver-specific encodings/transformations. 
    
    public static Random getRandomGen() {
        if (randomGen == null) {
            randomGen = new Random(seed);
        }
        return randomGen;
    }
    public static boolean getVerbose() {
        return verbose;
    }
    
    public static void setVerbose(boolean v) {
        verbose = v;
    }
    
    public static void setMinion(String m) {
        minionpath=m;
    }
    public static String getMinion() {
        return minionpath;
    }
    public static String getFznSolver() {
        return fznpath;
    }
    
    public static void setSymDetect(String m) {
        symdetectpath=m;
    }
    public static String getSymDetect() {
        return symdetectpath;
    }
    public static String getSatSolver() {
        return satsolverpath;
    }
    public static boolean usingBoolector() {
        return smtsolver==SMTSOL.BOOLECTOR;
    }
    public static boolean usingZ3() {
        return smtsolver==SMTSOL.Z3;
    }
    public static boolean usingYices2() {
        return smtsolver==SMTSOL.YICES2;
    }
    public static String getSMTSolverPath() {
        return smtsolverpath;
    }
    public static String getSatFamily() {
        return satfamily;
    }
    
    public static boolean getRunSolver() {
        return runsolver;
    }
    
    public static void setRunSolver() {
        runsolver=true;
    }

    public static String getPreprocess() {
        return preprocess;
    }
    public static long getTimeLimit() {
        return timelimit; 
    }
    public static long getCNFLimit() {
        return cnflimit; 
    }
    public static void setCNFLimit(long dl) {
        cnflimit=dl;
    }
    
    // New command line flags
    public static void setEprimeFile(String s) {
        eprimefile=s;
    }
    public static void setParamFile(String s) {
        paramfile=s;
    }
    public static void setParamString(String s) {
        paramstring=s;
    }
    public static void setMinionFile(String s) {
        minionfile=s;
    }
    public static void setMinionSolutionFile(String s) {
        minionsolfile=s;
    }
    public static void setSolutionFile(String s) {
        solutionfile=s;
    }
    public static void setInfoFile(String s) {
        infofile=s;
    }
    public static void setAuxFile(String s) {
        auxfile=s;
    }
    public static void setFznFile(String s) {
        fznfile=s;
    }
    public static void setMinizincFile(String s) {
        minizincfile=s;
    }
    
    public static void printlnIfVerbose(Object o) {
        if (verbose) {
            System.out.println(o);
        }
    }
    
    public static String getMinionStatsTempFile() {
        return minionStatsTempFile;
    }
    public static String getMinionSolsTempFile() {
        return minionSolsTempFile;
    }
    public static void rmTempFiles() {
        File f;
        f = new File(CmdFlags.getMinionStatsTempFile());
        if (f.exists()) f.delete();
        f = new File(CmdFlags.getMinionSolsTempFile());
        if (f.exists()) f.delete();
        try {
            if (recordIntermediateObjectiveValues != null)
                recordIntermediateObjectiveValues.close();
        } catch (IOException e) {}
    }
    public static void createTempFiles() {
        try {
            // create the files with empty contents
            new PrintWriter(CmdFlags.getMinionStatsTempFile()).close();
            new PrintWriter(CmdFlags.getMinionSolsTempFile()).close();
        } catch(Exception e) {
        }
    }
    
    public static void setSolverExtraFlags(ArrayList<String> f) {
        if (solverflags == null) {
            solverflags = new ArrayList<String>();
        }
        for (String flag : f) {
            if (!flag.equals("")) {
                solverflags.add(flag);
            }
        }
    }
    public static ArrayList<String> getSolverExtraFlags() {
        if(solverflags==null) {
            return new ArrayList<String>();
        }
        else {
            return solverflags;
        }
    }
    public static void addSolverFlag(String flag) {
        if (solverflags == null) { solverflags = new ArrayList<>(); }
        solverflags.add(flag);
    }

    public static void setUseDeleteVars(boolean t) {
        use_delete_vars = t;
    }
    
    public static boolean getUseDeleteVars() {
        return use_delete_vars;
    }
    
    public static boolean getWarnUndef() {
        return warn_undef;
    }
    
    // Output ready flag -- currently only controls simplifier in Times.  
    public static void setOutputReady(boolean b) {
        output_ready=b;
    }
    public static boolean getOutputReady() {
        return output_ready;
    }
    // After Aggregate flag -- controls removal of not-equal constraints.   
    public static void setAfterAggregate(boolean b) {
        after_aggregate=b;
    }
    public static boolean getAfterAggregate() {
        return after_aggregate;
    }
    
    public static void setUsePropagate(boolean t) {
        use_propagate = t;
    }
    
    public static boolean getUsePropagate() {
        return use_propagate;
    }
    
    public static void setUsePropagateExtend(boolean t) {
        use_propagate_extend = t;
    }
    
    public static boolean getUsePropagateExtend() {
        return use_propagate_extend;
    }
    
    public static void setRemoveRedundantVars(boolean t) {
        remove_redundant_vars = t;
    }
    public static boolean getRemoveRedundantVars() {
        return remove_redundant_vars;
    }
    
    public static void setAuxNonFunctional(boolean t) {
        aux_non_functional = t;
    }
    public static boolean getAuxNonFunctional() {
        return aux_non_functional;
    }
    
    public static void setUseAggregate(boolean t) {
        use_aggregate = t;
    }
    
    public static boolean getUseAggregate() {
        return use_aggregate;
    }
    
    public static void setUseVarSymBreaking(boolean t) {
        use_var_symmetry_breaking = t;
    }
    
    public static boolean getUseVarSymBreaking() {
        return use_var_symmetry_breaking;
    }
    public static boolean getExpandShortTab() {
        return expand_short_tab;
    }
    
    public static void setFindAllSolutions(boolean t) {
        if(t) {
            find_num_solutions=0;
        }
        else {
            find_num_solutions=1;  // Revert to default state of 1 solution.
        }
    }
    
    public static boolean getFindAllSolutions() {
        return find_num_solutions==0;
    }

    public static boolean getSolutionsToStdoutOneLine() {
        return solutions_to_stdout_one_line;
    }
    
    public static void setSolutionsToStdoutOneLine(boolean t) {
        solutions_to_stdout_one_line = t;
    }
    
    public static void setSolutionsToStdout(boolean t) {
        solutions_to_stdout = t;
    }
    
    public static boolean getSolutionsToStdout() {
        return solutions_to_stdout;
    }
    
    public static void setSolutionsToNull(boolean t) {
        solutions_to_null = t;
    }
    
    public static boolean getSolutionsToNull() {
        return solutions_to_null;
    }
    
    public static void setKeepDimacsFile(boolean t) {
        keep_dimacs_file = t;
    }
    
    public static boolean getKeepDimacsFile() {
        return keep_dimacs_file;
    }
    
    public static void setFindNumSolutions(long t) {
        find_num_solutions = t;
    }
    
    public static long getFindNumSolutions() {
        return find_num_solutions;
    }

    public static void setRecordIntermediateObjectiveValues(String filename) {
        try {
            recordIntermediateObjectiveValues = new FileWriter(filename);
        } catch (IOException e) {
            System.err.println("Cannot create file: " + filename);
            recordIntermediateObjectiveValues = null;
        }
    }

    public static void recordIntermediateObjectiveValue(long value) {
        if (recordIntermediateObjectiveValues != null) {
            double time = (((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000);
            try {
                recordIntermediateObjectiveValues.write(value + "\t" + time + "\n");
            } catch (IOException e) {
                System.err.println("Cannot write to the file that was specified with flag -record-intermediate-objective-values");
            }
        }
    }
    
    public static boolean recordObjectiveValues() {
        return recordIntermediateObjectiveValues != null;
    }
    
    public static void setUseBoundVars(boolean t) {
        use_boundvars = t;
    }
    
    public static boolean getUseBoundVars() {
        return use_boundvars;
    }
    
    public static boolean getGecodetrans() {
        return soltype==SolEnum.GECODE;
    }
    
    public static boolean getChuffedtrans() {
        return soltype==SolEnum.CHUFFED;
    }
    public static boolean getOrtoolstrans() {
        return soltype==SolEnum.ORTOOLS;
    }
    
    public static boolean getFlatzinctrans() {
        return soltype==SolEnum.FZNSTD || soltype==SolEnum.GECODE || soltype==SolEnum.CHUFFED || soltype==SolEnum.ORTOOLS;
    }
    
    public static boolean getMiniontrans() {
        return soltype==SolEnum.MINION || soltype==SolEnum.MINIONSNS;
    }
    
    public static boolean getMinionSNStrans() {
        return soltype==SolEnum.MINIONSNS;
    }
    
    public static boolean getMinizinctrans() {
        return soltype==SolEnum.MINIZINC;
    }
    
    public static boolean getSattrans() {
        return soltype==SolEnum.SAT || soltype==SolEnum.MAXSAT || soltype==SolEnum.SMT;
    }
    public static boolean getSMTtrans() {
        return soltype==SolEnum.SMT;
    }
    public static boolean getMaxsattrans() {
        return soltype==SolEnum.MAXSAT;
    }
    public static SumEnc getSatPBEnc() {
        return pb_encoding;
    }
    public static SumEnc getSatSumEnc() {
        return sum_encoding;
    }
    public static void setUseCSE(boolean m) {
        use_cse=m;
    }
    public static boolean getUseCSE() {
        return use_cse;
    }
    public static void setUseACCSE(boolean m) {
        use_ac_cse=m;
    }
    public static boolean getUseACCSE() {
        return use_ac_cse;
    }
    public static void setUseActiveACCSE2(boolean m) {
        use_active_ac_cse2=m;
        if(m) use_ac_cse=true;  // Make sure AC-CSE is switched on when switching on active AC-CSE. 
    }
    public static boolean getUseActiveACCSE2() {
        return use_active_ac_cse2;
    }
    public static void setUseActiveACCSE(boolean m) {
        use_active_ac_cse=m;
        if(m) use_ac_cse=true;  // Make sure AC-CSE is switched on when switching on active AC-CSE. 
    }
    public static boolean getUseActiveACCSE() {
        return use_active_ac_cse;
    }
    
    public static void setUseActiveCSE(boolean m) {
        use_active_cse=m;
    }
    public static boolean getUseActiveCSE() {
        return use_active_cse;
    }
    public static void setUseACCSEAlt(boolean m) {
        use_ac_cse_alt=m;
    }
    public static boolean getUseACCSEAlt() {
        return use_ac_cse_alt;
    }

    public static LOGIC getLogic() {
        return logic;
    }
    
    public static void setBvTraversal(boolean traverse) { bvTraversal =traverse; }
    public static boolean getBvTraversal() { return bvTraversal; }
    public static boolean getUseUF() { return logic == LOGIC.QF_UF; }
    public static boolean getUseBV() { return logic == LOGIC.QF_BV; }
    public static boolean getUseIDL() { return logic == LOGIC.QF_IDL; }
    public static boolean getUseLIA() { return logic == LOGIC.QF_LIA; }
    public static boolean getUseNIA() { return logic == LOGIC.QF_NIA; }
    public static boolean getUseInt() { return logic == LOGIC.QF_LIA || logic == LOGIC.QF_IDL || logic==LOGIC.QF_NIA; }
    public static boolean getUseFlat() { return encoding == ENCODING.FLAT; }
    public static boolean getUseNested() { return encoding == ENCODING.NESTED; }
    public static boolean getSMTEncodeObjective() {
        return usingZ3() && (getUseBV() || getUseNIA() || getUseLIA() || getUseIDL());
    }
    public static boolean SMTDecompAlldiff() {
        if(getUseUF()) {
            return true;
        }
        return smt_decomp_alldiff;
    }
    public static boolean SMTPairwiseAlldiff() {
        return smt_pairwise_alldiff;
    }
    public static boolean getUseAuxSMT() {
        return aux_smt;
    }
    public static int getMode() {
        return mode;
    }
    public static void setMode(int newmode) {
        mode=newmode;
    }
    public static boolean getOptWarmStart() {
        return opt_warm_start;
    }
    public static String getOptStrategy() {
        return opt_strategy;
    }
    public static boolean getGraphColSymBreak() {
        return graph_col_sym_break;
    }
    public static void setSaveSymbols() {
        save_symbols=true;
    }
    public static boolean getSaveSymbols() {
        return save_symbols;
    }
    // Print if not in completely silent mode.
    public static void println(Object o) {
        System.out.println(o);
    }
    
    //  Print error message to stderr and bail out. 
    public static void errorExit(String errmsg) {
        System.err.println("ERROR: "+errmsg);
        CmdFlags.exit();
    }
    public static void errorExit(String errmsg1, String errmsg2) {
        System.err.println("ERROR: "+errmsg1);
        System.err.println("ERROR: "+errmsg2);
        CmdFlags.exit();
    }
    public static void errorExit(String errmsg1, String errmsg2, String errmsg3) {
        System.err.println("ERROR: "+errmsg1);
        System.err.println("ERROR: "+errmsg2);
        System.err.println("ERROR: "+errmsg3);
        CmdFlags.exit();
    }
    public static void warning(String warn) {
        System.err.println("WARNING: "+warn);
    }
    
    public static void cmdLineExit(String errmsg) {
        System.err.println("ERROR: "+errmsg);
        System.err.println("For command line help, use the -help flag.");
        CmdFlags.exit();
    }

    //Used when a NIA solver returns unknown
    public static void unknownExit() {
        rmTempFiles();
        System.exit(178);
    }

    public static void typeError(String errmsg1) {
        System.err.println("ERROR: "+errmsg1);
    }
    // Exit with non-zero code. 
    public static void exit() {
        rmTempFiles();
        System.exit(1);
    }
    
    public static void parseArguments(String[] args) {
        ArrayList<String> arglist=new ArrayList<String>();
        // The default optimisation level is -O2 so put this on the start of the list 
        arglist.add("-O2");
        //  Default symmetry breaking level is -S1 so put that at the start.
        arglist.add("-S1");
        arglist.addAll(Arrays.asList(args));
        
        // First do the -O switches. The rightmost one is the one that takes
        // effect. 
        
        for(int i=0; i<arglist.size(); i++) {
            String cur=arglist.get(i);
            // Optimisation level options.
            // These (like all other command-line switches)
            // override other -O switches specified earlier in the command line. 
            if(cur.equals("-O0") || cur.equals("-O1") || cur.equals("-O2") || cur.equals("-O3")) {
                arglist.remove(i);
                i--;
                if(cur.equals("-O0")) {
                    // Switch all optimisations off.
                    CmdFlags.setUseCSE(false);
                    CmdFlags.setUseActiveCSE(false);
                    CmdFlags.setUseACCSE(false);
                    CmdFlags.setUseACCSEAlt(false);
                    
                    CmdFlags.setUseDeleteVars(false);
                    CmdFlags.setUsePropagate(false);
                    CmdFlags.setUsePropagateExtend(false);
                    CmdFlags.setUseAggregate(false);
                    make_short_tab=2;
                }
                else if(cur.equals("-O1")) {
                    // Switch basic ones on. 
                    CmdFlags.setUseCSE(true);
                    CmdFlags.setUseActiveCSE(true);
                    CmdFlags.setUseACCSE(false);
                    CmdFlags.setUseACCSEAlt(false);
                    
                    CmdFlags.setUseDeleteVars(true);
                    CmdFlags.setUsePropagate(false);
                    CmdFlags.setUsePropagateExtend(false);
                    CmdFlags.setUseAggregate(false);
                    make_short_tab=2;
                }
                else if(cur.equals("-O2")) {
                    // Default settings.
                    CmdFlags.setUseCSE(true);
                    CmdFlags.setUseActiveCSE(true);
                    CmdFlags.setUseACCSE(false);
                    CmdFlags.setUseACCSEAlt(false);
                    
                    CmdFlags.setUseDeleteVars(true);
                    CmdFlags.setUsePropagate(true);
                    CmdFlags.setUsePropagateExtend(true);
                    CmdFlags.setUseAggregate(true);
                    make_short_tab=2;
                }
                else if(cur.equals("-O3")) {
                    // Most powerful settings.
                    CmdFlags.setUseCSE(true);
                    CmdFlags.setUseActiveCSE(true);
                    CmdFlags.setUseACCSE(true);
                    CmdFlags.setUseACCSEAlt(false);
                    
                    CmdFlags.setUseDeleteVars(true);
                    CmdFlags.setUsePropagate(true);
                    CmdFlags.setUsePropagateExtend(true);
                    CmdFlags.setUseAggregate(true);
                    make_short_tab=3; //  Tabulate as in CP'18 paper.
                }
            }
        }
        
        for(int i=0; i<arglist.size(); i++) {
            String cur=arglist.get(i);
            // Symmetry/dominance level options.
            // These (like all other command-line switches)
            // override other -S switches specified earlier in the command line. 
            if(cur.equals("-S0") || cur.equals("-S1") || cur.equals("-S2")) {
                arglist.remove(i);
                i--;
                if(cur.equals("-S0")) {
                    setRemoveRedundantVars(false);
                    setAuxNonFunctional(false);
                    setUseVarSymBreaking(false);
                    short_tab_sat_extra=true;
                }
                else if(cur.equals("-S1")) {
                    //  Lightweight optimisations that can reduce SAT encoding size/CP model size
                    //  Changes number of solutions.
                    setRemoveRedundantVars(true);
                    setAuxNonFunctional(true);
                    setUseVarSymBreaking(false);
                    short_tab_sat_extra=false;
                }
                else if(cur.equals("-S2")) {
                    //  Heavier optimisations. Includes -S1 and -var-sym-breaking
                    setRemoveRedundantVars(true);
                    setAuxNonFunctional(true);
                    setUseVarSymBreaking(true);
                    short_tab_sat_extra=false;
                }
            }
        }
        
        // Parse remaining arguments left-to-right. 
        
        while(arglist.size()>0) {
            String cur=arglist.remove(0);
            
            if(cur.equals("-help")) {
                HelpText.printHelp();
                System.exit(0);
            }
            // verbose mode. 
            else if(cur.equals("-v")) {
                CmdFlags.setVerbose(true);
                CmdFlags.verbose_make_short = true;
            }
            
            // Reformulation options -- CSE
            else if(cur.equals("-no-cse")) {
                // Switch off all kinds of CSE.
                CmdFlags.setUseCSE(false);
                CmdFlags.setUseActiveCSE(false);
                CmdFlags.setUseACCSE(false);
                CmdFlags.setUseACCSEAlt(false);
            }
            else if(cur.equals("-identical-cse")) {
                // Switch on identical CSE only. 
                CmdFlags.setUseCSE(true);
            }
            else if(cur.equals("-active-cse")) {
                CmdFlags.setUseActiveCSE(true);
            }
            else if(cur.equals("-ac-cse")) {
                CmdFlags.setUseACCSE(true);
            }
            else if(cur.equals("-active-ac-cse")) {
                CmdFlags.setUseActiveACCSE(true);
            }
            else if(cur.equals("-active-ac-cse2")) {
                CmdFlags.setUseActiveACCSE2(true);
            }
            else if(cur.equals("-ac-cse-heuristic")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("AC-CSE heuristic integer missing");
                accse_heuristic=Integer.parseInt(arglist.remove(0));
            }
            else if(cur.equals("-ac-cse-alt")) {
                CmdFlags.setUseACCSEAlt(true);
            }

            // SMT Logics
            else if (cur.equals("-smt-no-logic")) {
                logic=LOGIC.QF_UF;
            }
            else if (cur.equals("-smt-idl")) {
                logic=LOGIC.QF_IDL;
            }
            else if (cur.equals("-smt-lia")) {
                logic=LOGIC.QF_LIA;
            }
            else if (cur.equals("-smt-bv")) {
                logic=LOGIC.QF_BV;
            }
            else if (cur.equals("-smt-nia")) {
                logic=LOGIC.QF_NIA;
            }
            else if (cur.equals("-smt-flat")) {
                encoding=ENCODING.FLAT;
            }
            else if (cur.equals("-smt-nested")) {
                encoding=ENCODING.NESTED;
            }
            else if (cur.equals("-z3")) {
                if(smtsolver!=SMTSOL.DEFAULT) {
                    cmdLineExit("Multiple SMT solvers specified on command-line.");
                }
                smtsolver=SMTSOL.Z3; 
            }
            else if (cur.equals("-boolector")) {
                if(smtsolver!=SMTSOL.DEFAULT) {
                    cmdLineExit("Multiple SMT solvers specified on command-line.");
                }
                smtsolver=SMTSOL.BOOLECTOR; 
            }
            else if (cur.equals("-yices2")) {
                if(smtsolver!=SMTSOL.DEFAULT) {
                    cmdLineExit("Multiple SMT solvers specified on command-line.");
                }
                smtsolver=SMTSOL.YICES2; 
            }
            else if(cur.equals("-smtsolver-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing SMT solver path following -smtsolver-bin");
                smtsolverpath=arglist.remove(0);
                CmdFlags.warning("-smtsolver-bin is deprecated.");
            }
            // SMT Auxiliary variables
            else if (cur.equals("-aux-smt")) {
                aux_smt=true;
            }
            
            // Decompose AllDiff constraints
            else if (cur.equals("-smt-no-decomp-alldiff")) {
                smt_decomp_alldiff=false;
            }
            else if(cur.equals("-smt-pairwise-alldiff")) {
                smt_pairwise_alldiff=true;   //  Use pairwise instead of linear alldiff decomp. 
            }
            
            // Model improvement. 
            
            else if(cur.equals("-deletevars")) {
                setUseDeleteVars(true);
            }
            else if(cur.equals("-aggregate")) {
                setUseAggregate(true);
            }
            else if(cur.equals("-reduce-domains")) {
                setUsePropagate(true);
            }
            else if(cur.equals("-reduce-domains-extend")) {
                setUsePropagate(true);
                setUsePropagateExtend(true);
            }
            else if(cur.equals("-remove-redundant-vars")) {
                setRemoveRedundantVars(true);
            }
            else if(cur.equals("-aux-non-functional")) {
                setAuxNonFunctional(true);
            }
            else if(cur.equals("-graph-col-sym-break")) {
                graph_col_sym_break=true;
            }
            else if(cur.equals("-opt-warm-start")) {
                opt_warm_start=true;
            }
            else if(cur.equals("-opt-strategy")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Optimisation strategy missing after -opt-strategy flag");
                opt_strategy=arglist.remove(0);
                
                if(! (opt_strategy.equals("linear") || opt_strategy.equals("unsat") || opt_strategy.equals("bisect"))) CmdFlags.cmdLineExit("Optimisation strategy must be linear, unsat or bisect.");
            }
            else if(cur.equals("-make-tab")) {
                make_tab=true;
                int scopesize=Integer.parseInt(arglist.remove(0));
                make_tab_scope=scopesize;
            }
            else if(cur.equals("-table-squash")) {
              if(arglist.size()==0) CmdFlags.cmdLineExit("-table-squash expects an argument");
              table_squash = Integer.parseInt(arglist.remove(0));
            }
            else if(cur.equals("-v-make-short")) {
              verbose_make_short = true;
            }
            else if(cur.equals("-preprocess")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("-preprocess expects an argument. Options are: None, GAC, SACBounds, SACBounds_limit, SAC, SAC_limit, SSAC, SSAC_limit, SSACBounds, SSACBounds_limit.");
                preprocess=arglist.remove(0);
            }
            else if(cur.equals("-timelimit")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("-timelimit expects an argument in seconds.");
                timelimit=Integer.parseInt(arglist.remove(0))*1000;  // Convert to millis. 
            }
            else if(cur.equals("-cnflimit")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("-cnflimit expects an integer argument.");
                CmdFlags.setCNFLimit(Integer.parseInt(arglist.remove(0)));
            }
            
            // For experiments -- prime the virtual machine by running the translation 
            // a few times before taking a timing. 
            else if(cur.equals("-dryruns")) {
                dryruns=true;
            }
            else if(cur.equals("-test-solutions")) {
                test_solutions=true;
            }
            else if(cur.equals("-run-solver")) {
                CmdFlags.setRunSolver();
            }
            else if(cur.equals("-all-solutions")) {
                CmdFlags.setFindAllSolutions(true);
            }
            else if(cur.equals("-num-solutions")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("-num-solutions expects an argument: the number of solutions required.");
                long numsols=Long.parseLong(arglist.remove(0));
                if(numsols<=0) CmdFlags.cmdLineExit("Argument to -num-solutions is less than one.");
                CmdFlags.setFindNumSolutions(numsols);
            }
            else if(cur.equals("-solutions-to-stdout-one-line")) {
                CmdFlags.setSolutionsToStdoutOneLine(true);
            }
            else if(cur.equals("-solutions-to-stdout")) {
                CmdFlags.setSolutionsToStdout(true);
            }
            else if(cur.equals("-solutions-to-null")) {
                CmdFlags.setSolutionsToNull(true);
            }
            else if(cur.equals("-keep-dimacs-file")) {
                CmdFlags.setKeepDimacsFile(true);
            }
            else if(cur.equals("-record-intermediate-objective-values")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("File name missing following -record-intermediate-objective-values");
                CmdFlags.setRecordIntermediateObjectiveValues(arglist.remove(0));
            }
            else if(cur.equals("-output-all-sols")) {
                output_all_sols=true;
            }
            else if(cur.equals("-no-bound-vars")) {
                setUseBoundVars(false);
            }
            else if(cur.equals("-minion-boundvar-threshold")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("-minion-boundvar-threshold expects an integer argument.");
                int boundvar_threshold = Integer.valueOf(arglist.remove(0));
                if(boundvar_threshold <= 0)
                    CmdFlags.cmdLineExit("Argument to -minion-boundvar-threshold is less than one.");
                Constants.boundvar_threshold = boundvar_threshold;
            }
            else if(cur.equals("-var-sym-breaking")) {
                setUseVarSymBreaking(true);
            }
            else if(cur.equals("-expand-short-tab")) {
                expand_short_tab=true;
            }
            else if(cur.equals("-make-short-tab")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing short-table mode after -make-short-tab");
                CmdFlags.make_short_tab=Integer.valueOf(arglist.remove(0));
            }
            else if(cur.equals("-short-tab-sat-extra")) {
                short_tab_sat_extra=true;
            }
            else if(cur.equals("-tabulate")) {
                make_short_tab=3;
            }
            else if(cur.equals("-tabulate-opt")) {
                tabulate_opt=true;
            }
            else if(cur.equals("-element-gac")) {
                element_gac=true;
            }
            else if(cur.equals("-tabulate2")) {
                tabulate2=true;
            }
            else if(cur.equals("-tabulate-diagnostics")) {
                tabulate_diagnostics=true;
            }
            else if(cur.equals("-tab-nolimit")) {
                tabulate_nolimit=true;
            }
            else if(cur.equals("-factor-encoding")) {
                factor_encoding=true;
                if(arglist.size()>0) {
                    try {
                        factor_encoding_mode=Integer.parseInt(arglist.get(0));
                        arglist.remove(0);  // If parsing successful.
                    }
                    catch(NumberFormatException e) {
                    }
                }
            }
            
            // Warnings
            else if(cur.equals("-Wundef")) {
                warn_undef=true;
            }
            
            // Outputs
            else if(cur.equals("-minion")) {
                if(soltype!=SolEnum.DEFAULT) CmdFlags.cmdLineExit("Two backend solvers specified on command line.");
                soltype=SolEnum.MINION;
            }
            else if(cur.equals("-gecode")) {
                if(soltype!=SolEnum.DEFAULT) CmdFlags.cmdLineExit("Two backend solvers specified on command line.");
                soltype=SolEnum.GECODE;
            }
            else if(cur.equals("-chuffed")) {
                if(soltype!=SolEnum.DEFAULT) CmdFlags.cmdLineExit("Two backend solvers specified on command line.");
                soltype=SolEnum.CHUFFED;
            }
            else if(cur.equals("-or-tools")) {
                if(soltype!=SolEnum.DEFAULT) CmdFlags.cmdLineExit("Two backend solvers specified on command line.");
                soltype=SolEnum.ORTOOLS;
            }
            else if(cur.equals("-flatzinc")) {
                if(soltype!=SolEnum.DEFAULT) CmdFlags.cmdLineExit("Two backend solvers specified on command line.");
                soltype=SolEnum.FZNSTD;
            }
            else if(cur.equals("-minizinc")) {
                if(soltype!=SolEnum.DEFAULT) CmdFlags.cmdLineExit("Two backend solvers specified on command line.");
                soltype=SolEnum.MINIZINC;
            }
            else if(cur.equals("-sat")) {
                if(soltype!=SolEnum.DEFAULT) CmdFlags.cmdLineExit("Two backend solvers specified on command line.");
                soltype=SolEnum.SAT;
            }
            else if(cur.equals("-maxsat")) {
                if(soltype!=SolEnum.DEFAULT) CmdFlags.cmdLineExit("Two backend solvers specified on command line.");
                soltype=SolEnum.MAXSAT;
            }
            else if(cur.equals("-smt")) {
                if(soltype!=SolEnum.DEFAULT) CmdFlags.cmdLineExit("Two backend solvers specified on command line.");
                soltype=SolEnum.SMT;
            }
            else if(cur.equals("-mip")) {
                if(soltype!=SolEnum.DEFAULT) CmdFlags.cmdLineExit("Two backend solvers specified on command line.");
                soltype=SolEnum.MIP;
            }
            else if(cur.equals("-sns")) {
                if(soltype!=SolEnum.DEFAULT) CmdFlags.cmdLineExit("Two backend solvers specified on command line.");
                soltype=SolEnum.MINIONSNS;
            }
            else if (cur.equals("-dom-flatten-strategy")){
                if(arglist.size()==0) CmdFlags.cmdLineExit("Strategy missing after -dom-flatten-strategy flag");
                dom_flatten_strategy=arglist.remove(0);
                if(! (dom_flatten_strategy.equals("full") || dom_flatten_strategy.equals("semi") || dom_flatten_strategy.equals("basic"))) CmdFlags.cmdLineExit("dom_flatten_strategy must be full, semi or basic.");
            }
            else if(cur.equals("-sat-polarity")) {
                use_polarity=true;
            }
            else if(cur.equals("-sat-pb-mdd")) {
                pb_encoding=SumEnc.MDD;    // pseudo-Boolean constraints -> AMO-MDD
            }
            else if(cur.equals("-sat-sum-mdd")) {
                sum_encoding=SumEnc.MDD;   // sums not PB -> AMO-MDD
            }
            else if(cur.equals("-sat-pb-gpw")) {
                pb_encoding=SumEnc.GPW;    // pseudo-Boolean constraints -> AMO-GPW
            }
            else if(cur.equals("-sat-sum-gpw")) {
                sum_encoding=SumEnc.GPW;   // sums not PB -> AMO-GPW
            }
            else if(cur.equals("-sat-pb-lpw")) {
                pb_encoding=SumEnc.LPW;    // pseudo-Boolean constraints -> AMO-LPW
            }
            else if(cur.equals("-sat-sum-lpw")) {
                sum_encoding=SumEnc.LPW;   // sums not PB -> AMO-LPW
            }
            else if(cur.equals("-sat-pb-swc")) {
                pb_encoding=SumEnc.SWC;    // pseudo-Boolean constraints -> AMO-SWC
            }
            else if(cur.equals("-sat-sum-swc")) {
                sum_encoding=SumEnc.SWC;   // sums not PB -> AMO-SWC
            }
            else if(cur.equals("-sat-pb-ggt")) {
                pb_encoding=SumEnc.GGT;    // pseudo-Boolean constraints -> AMO-GGT
            }
            else if(cur.equals("-sat-sum-ggt")) {
                sum_encoding=SumEnc.GGT;   // sums not PB -> AMO-GGT
            }
            else if(cur.equals("-sat-pb-tree")) {
                pb_encoding=SumEnc.TREE;    // pseudo-Boolean constraints -> AMO-GGT
            }
            else if(cur.equals("-sat-sum-tree")) {
                sum_encoding=SumEnc.TREE;   // sums not PB -> AMO-GGT
            }
            else if(cur.equals("-sat-pb-rggt")) {
                pb_encoding=SumEnc.RGGT;    // pseudo-Boolean constraints -> AMO-RGGT
            }
            else if(cur.equals("-sat-sum-rggt")) {
                sum_encoding=SumEnc.RGGT;   // sums not PB -> AMO-RGGT
            }
            else if(cur.equals("-sat-pb-ggth")) {
                pb_encoding=SumEnc.GGTH;    // pseudo-Boolean constraints -> AMO-GGTH
            }
            else if(cur.equals("-sat-sum-ggth")) {
                sum_encoding=SumEnc.GGTH;   // sums not PB -> AMO-GGTH
            }
            else if(cur.equals("-sat-pb-gmto")) {
                pb_encoding=SumEnc.GMTO;    // pseudo-Boolean constraints -> AMO-GMTO
            }
            else if(cur.equals("-sat-sum-gmto")) {
                sum_encoding=SumEnc.GMTO;   // sums not PB -> AMO-GMTO
            }
            else if(cur.equals("-rggt-mutex")) {
                rggt_mutex=true;
            }
            else if(cur.equals("-rggt-stats")) {
                rggt_stats=true;
            }
            else if(cur.equals("-rggt-reduce")) {
                rggt_reduce=true;
            }
            else if(cur.equals("-amo-detect")) {
                amo_detect=true;    //  AMO detect flag now switches on both EO and AMO
            }
            else if(cur.equals("-amo-detect-override")) {
                amo_detect_override=true;    //  override amo groups given in pbamo constraints. 
            }
            else if(cur.equals("-amo-detect-strong")) {
                amo_detect=true;
                amo_detect_strong=true;    //  AMO detect flag now switches on both EO and AMO
            }
            else if(cur.equals("-sat-amo-commander")) {
                sat_amo_encoding=AMOEnc.COMMANDER;
            }
            else if(cur.equals("-sat-amo-tree")) {
                sat_amo_encoding=AMOEnc.TREE;
            }
            else if(cur.equals("-sat-amo-product")) {
                sat_amo_encoding=AMOEnc.PRODUCT;
            }
            else if(cur.equals("-sat-amo-ladder")) {
                sat_amo_encoding=AMOEnc.LADDER;
            }
            else if(cur.equals("-sat-amo-pairwise")) {
                sat_amo_encoding=AMOEnc.PAIRWISE;
            }
            else if(cur.equals("-sat-amo-bimander")) {
                sat_amo_encoding=AMOEnc.BIMANDER;
                if(arglist.size()>0) {
                    try {
                        bimander_g=Integer.parseInt(arglist.get(0));
                        arglist.remove(0);  // If parsing successful.
                    }
                    catch(NumberFormatException e) {
                    }
                }
            }
            else if(cur.equals("-sat-table-mdd")) {
                sat_table_mdd=true;
            }
            else if(cur.equals("-sat-matrixderef-decomp")) {
                sat_matrixderef_decomp=true;
            }
            else if(cur.equals("-sat-element-gac")) {
                sat_element_gac=true;
            }
            else if(cur.equals("-minion-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing Minion executable file name following -minion-bin");
                CmdFlags.setMinion(arglist.remove(0));
            }
            else if(cur.equals("-boolector-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing Boolector solver executable file name following -boolector-bin");
                boolectorpath=arglist.remove(0);
            }
            else if(cur.equals("-z3-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing Z3 solver executable file name following -z3-bin");
                z3path=arglist.remove(0);
            }
            else if(cur.equals("-yices2-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing Yices2 solver executable file name following -yices2-bin");
                yicespath=arglist.remove(0);
            }
            else if(cur.equals("-smt-seed")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing seed value following -smt-seed");
                smtseed=arglist.remove(0);
            }
            else if(cur.equals("-satsolver-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing SAT solver executable file name following -satsolver-bin");
                satsolverpath=arglist.remove(0);
            }
            else if(cur.equals("-kissat-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing SAT solver executable file name following -kissat-bin");
                kissatpath=arglist.remove(0);
            }
            else if(cur.equals("-sat-output-mapping")) {
                satoutputmapping=true;
            }

            else if(cur.equals("-sat-family")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing SAT family name following -sat-family");
                String sf=arglist.remove(0);
                if(! ( sf.equals("minisat") || sf.equals("lingeling") || sf.equals("glucose") || sf.equals("cadical") || sf.equals("kissat")
                        || sf.equals("nbc_minisat_all") || sf.equals("bc_minisat_all"))) {
                            CmdFlags.cmdLineExit("SAT family "+sf+" not supported.");
                }
                if(sf.equals("nbc_minisat_all") || sf.equals("bc_minisat_all")) {
                    CmdFlags.setFindAllSolutions(true); // if minisat_all directly set all sol flag
                }
                satfamily=sf;
            }
            else if(cur.equals("-solver-options")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing solver options string");
                ArrayList<String> temp=new ArrayList<String>(Arrays.asList(arglist.remove(0).split(" ")));
                for(int i=0; i<temp.size(); i++) {
                    if(temp.get(i).equals("")) {
                        temp.remove(i); i--;
                    }
                }
                CmdFlags.setSolverExtraFlags(temp);
            }
            else if(cur.equals("-gecode-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing Gecode executable file name");
                gecodepath=arglist.remove(0);
            }
            else if(cur.equals("-chuffed-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing Chuffed executable file name");
                chuffedpath=arglist.remove(0);
            }
            else if(cur.equals("-or-tools-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing OR Tools executable file name");
                ortoolspath=arglist.remove(0);
            }
            else if(cur.equals("-fzn-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing flatzinc solver executable file name");
                fznpath = arglist.remove(0);
            }
            else if(cur.equals("-symdetect-bin")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing symmetry_detect executable file name");
                CmdFlags.setSymDetect(arglist.remove(0));
            }
            else if(cur.equals("-in-eprime")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Essence Prime model file name missing after -in-eprime");
                
                CmdFlags.setEprimeFile(arglist.remove(0));
            }
            else if(cur.equals("-in-param")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Essence Prime parameter file missing after -in-param");
                
                CmdFlags.setParamFile(arglist.remove(0));
            }
            else if(cur.equals("-params")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Parameter string missing after -params");
                
                CmdFlags.setParamString(arglist.remove(0));
            }
            else if (cur.equals("-out-prefix")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("prefix missing after -out-prefix");
                
                String prefix = arglist.remove(0);
                        CmdFlags.setMinionFile(prefix+".minion");
                satfile = prefix+".dimacs";
                smtfile = prefix+".smt2";
                CmdFlags.setMinizincFile(prefix+".mzn");
                CmdFlags.setSolutionFile(prefix+".solution");
                CmdFlags.setInfoFile(prefix+".info");
                CmdFlags.setAuxFile(prefix+".aux");
                CmdFlags.setMinionSolutionFile(prefix+".minionsolution");
                CmdFlags.setFznFile(prefix+".fzn");
            }
            else if(cur.equals("-out-minion")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Minion output file name missing after -out-minion");
                
                CmdFlags.setMinionFile(arglist.remove(0));
            }
            else if(cur.equals("-out-sat")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("SAT output file name missing after -out-sat");
                satfile=arglist.remove(0);
            }
            else if(cur.equals("-out-smt")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("SMT output file name missing after -out-smt");
                smtfile=arglist.remove(0);
            }
            else if(cur.equals("-out-minizinc")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Minizinc output file name missing after -out-minizinc");
                
                CmdFlags.setMinizincFile(arglist.remove(0));
            }
            else if(cur.equals("-out-solution")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Solution file name missing following -out-solution");
                
                CmdFlags.setSolutionFile(arglist.remove(0));
            }
            else if(cur.equals("-out-info")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Statistics file name missing following -out-info");
                
                CmdFlags.setInfoFile(arglist.remove(0));
            }
            else if(cur.equals("-out-aux")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Aux file name missing after -out-aux");
                
                CmdFlags.setAuxFile(arglist.remove(0));
            }
            else if(cur.equals("-minion-sol-file")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing Minion solution file name after -minion-sol-file");
                
                CmdFlags.setMinionSolutionFile(arglist.remove(0));
            }
            else if(cur.equals("-out-flatzinc")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing FlatZinc output file name after -out-flatzinc");
                
                CmdFlags.setFznFile(arglist.remove(0));
            }
            else if(cur.equals("-seed")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing value for seed");
                seed=Integer.parseInt(arglist.remove(0));
            }
            else if(cur.equals("-param-to-json")) {
                param_to_json=true;
            }
            else if(cur.equals("-save-symbols")) {
                CmdFlags.setSaveSymbols();
            }
            else if(cur.equals("-mode")) {
                if(arglist.size()==0) CmdFlags.cmdLineExit("Missing mode argument");
                
                String mode_st=arglist.remove(0);
                
                if(mode_st.equals("Normal")) {
                    setMode(Normal);
                }
                else if(mode_st.equals("ReadSolution")) {
                    setMode(ReadSolution);
                }
                else if(mode_st.equals("ReadDomainStore")) {
                    setMode(ReadDomainStore);
                }
                else {
                    CmdFlags.cmdLineExit("-mode argument not followed by Normal, ReadSolution, or ReadDomainStore.");
                }
            }
            
            // If a parameter is not parsed by any of the above cases,
            // try to guess whether it is the .eprime file or the .param file. 
            else if(cur.length()>=7 && cur.substring(cur.length()-7, cur.length()).equals(".eprime") && CmdFlags.eprimefile==null) {
                CmdFlags.eprimefile=cur;
            }
            
            else if(cur.length()>=6 && cur.substring(cur.length()-6, cur.length()).equals(".param") && CmdFlags.paramfile==null) {
                CmdFlags.paramfile=cur;
            }
            
            else if(cur.length()>=13 && cur.substring(cur.length()-13, cur.length()).equals(".eprime-param") && CmdFlags.paramfile==null) {
                CmdFlags.paramfile=cur;
            }
            
            else if(cur.equals("-cgroups")) {
                // just ignore
            }
            else if(cur.equals("-compress-doms")) {
                CmdFlags.compressDominance = true;
            }
            else if(cur.equals("-noblock-dom")) {
                CmdFlags.noblockDom = true;
            }
            else if(cur.equals("-interactive-solver")) {
                CmdFlags.interactiveSolver = true;
            }
            else if(cur.equals("-profile-wait")) {
                CmdFlags.warning("Busy-wait for 15 seconds for profiler to connect.");
                long starttime=System.currentTimeMillis();
                while(System.currentTimeMillis()-starttime < 15000) {
                    for(int i=0; i<1000000; i++) {
                        // busy wait loop
                    }
                }
            }
            else if(cur.equals("")) {
                //  ignore blank arguments. 
            }
            else {
                CmdFlags.cmdLineExit("Failed to parse the following argument: "+cur);
            }
        }
        
        //////////////////////////////////////////////////////////////////////////////////////////////////////
        //
        //   Finished parsing command-line arguments. Now do some checks. 
        
        
        //  Different checks for different modes.
        if(getMode()==Normal) {
            if(CmdFlags.eprimefile==null && !param_to_json) {
                CmdFlags.cmdLineExit("Not given Essence Prime model file.");
            }
            if(soltype==SolEnum.DEFAULT) {
                // Set default solver
                soltype=SolEnum.MINION;
            }
            if(fznpath==null) {
                //  Set default binaries for flatzinc solvers.  Default to chuffed for -flatzinc on cmdline
                if(soltype==SolEnum.GECODE) {
                    fznpath=gecodepath;
                }
                else if(soltype==SolEnum.ORTOOLS) {
                    fznpath=ortoolspath;
                }
                else {
                    fznpath=chuffedpath;
                }
            }
            if(!aux_non_functional) {
                //  -S0 on command-line, user has asked for number of solutions to be preserved.
                //  Warn about any non-default SAT encoding choices that might change the number of solutions. 
                if(pb_encoding!=SumEnc.DEFAULT || sum_encoding!=SumEnc.DEFAULT || sat_amo_encoding!=AMOEnc.DEFAULT || use_polarity || sat_table_mdd || (!short_tab_sat_extra)) {
                    CmdFlags.warning("-S0 on command-line, number of solutions should be preserved.");
                    CmdFlags.warning("However, a non-default SAT encoding has been selected, which may not preserve the number of solutions when using an external all-solutions solver (e.g. nbc_minisat_all).");
                }
            }
            if(find_num_solutions!=1) {
                //  -all-solutions or similar on the command-line
                if(pb_encoding!=SumEnc.DEFAULT || sum_encoding!=SumEnc.DEFAULT || sat_amo_encoding!=AMOEnc.DEFAULT || use_polarity || sat_table_mdd || (!short_tab_sat_extra) 
                    || getRemoveRedundantVars() || getAuxNonFunctional() || getUseVarSymBreaking()) {
                    CmdFlags.warning("Command-line arguments indicate more than one solution (e.g. -all-solutions).");
                    CmdFlags.warning("However, non-default SAT encodings or other options may change the number of solutions. Try -S0 and removing non-default SAT encodings if necessary.");
                }
            }
            if(sat_amo_encoding==AMOEnc.DEFAULT) {
                sat_amo_encoding=AMOEnc.PRODUCT;
            }
            if(pb_encoding==SumEnc.DEFAULT) {
                pb_encoding=SumEnc.TREE;
            }
            if(sum_encoding==SumEnc.DEFAULT) {
                sum_encoding=SumEnc.TREE;
            }
            // defaults for minion and other output files, and solution file name.
            if(CmdFlags.minionfile==null) {
                if(CmdFlags.paramfile!=null)
                    CmdFlags.minionfile=CmdFlags.paramfile+".minion";
                else
                    CmdFlags.minionfile=CmdFlags.eprimefile+".minion";
            }
            if(satfile==null) {
                if(paramfile!=null) {
                    satfile=paramfile+".dimacs";
                }
                else {
                    satfile=eprimefile+".dimacs";
                }
            }
            if(smtfile==null) {
                if(paramfile!=null) {
                    smtfile=paramfile+".smt2";
                }
                else {
                    smtfile=eprimefile+".smt2";
                }
            }
            if(CmdFlags.auxfile==null) {
                if(CmdFlags.paramfile!=null)
                    CmdFlags.auxfile=CmdFlags.paramfile+".aux";
                else
                    CmdFlags.auxfile=CmdFlags.eprimefile+".aux";
            }
            if(CmdFlags.fznfile==null) {
                if(CmdFlags.paramfile!=null)
                    CmdFlags.fznfile=CmdFlags.paramfile+".fzn";
                else
                    CmdFlags.fznfile=CmdFlags.eprimefile+".fzn";
            }
            if(CmdFlags.solutionfile==null) {
                if(CmdFlags.paramfile!=null)
                    CmdFlags.solutionfile=CmdFlags.paramfile+".solution";
                else
                    CmdFlags.solutionfile=CmdFlags.eprimefile+".solution";
            }
            if(infofile==null) {
                if(paramfile!=null)
                    infofile=paramfile+".info";
                else
                    infofile=eprimefile+".info";
            }
            if(CmdFlags.minizincfile==null) {
                if(CmdFlags.paramfile!=null)
                    CmdFlags.minizincfile=CmdFlags.paramfile+".mzn";
                else
                    CmdFlags.minizincfile=CmdFlags.eprimefile+".mzn";
            }
            if(CmdFlags.mipfile==null) {
                if(CmdFlags.paramfile!=null)
                    CmdFlags.mipfile=CmdFlags.paramfile+".lp";
                else
                    CmdFlags.mipfile=CmdFlags.eprimefile+".lp";
            }
            
            ///  Check and fill in missing parts of SAT configuration.
            if(getSattrans() && !getSMTtrans()) {
                if(getMaxsattrans()) {
                    if(satsolverpath==null) {
                        satsolverpath=maxsatpath;
                        // No need for satfamily in this case.
                    }
                }
                else {
                    //  Pure SAT, not MaxSAT or SMT
                    if(satfamily==null) {
                        if(satsolverpath==null) {
                            // Set defaults.
                            if(kissatpath!=null) {
                                satfamily="kissat";
                                satsolverpath=kissatpath;
                            }
                            else {
                                if(runsolver) {
                                    cmdLineExit("No SAT solver specified, and default solver (kissat) not found.");
                                }
                            }
                        }
                        else {
                            cmdLineExit("When -satsolver-bin is used, -sat-family is required as well.");
                        }
                    }
                    else if(satsolverpath==null) {
                        // satfamily is set but satsolverpath is not. 
                        // Case split for satfamily
                        if(satfamily.equals("kissat")) {
                            satsolverpath=(kissatpath==null)?"kissat":kissatpath;
                        }
                        else if(satfamily.equals("minisat") || satfamily.equals("lingeling") || satfamily.equals("glucose") || satfamily.equals("cadical")) {
                            satsolverpath=satfamily;  // Default value of sat solver is same as sat family. 
                        }
                        else if(satfamily.equals("nbc_minisat_all") || satfamily.equals("bc_minisat_all")) {
                            satsolverpath=satfamily+"_release";
                        }
                        else {
                            //  This should not be reachable. 
                            cmdLineExit("Unknown SAT solver family: "+satfamily);
                        }
                    }
                }
            }
            
            ///  Check and fill in missing parts of SMT configuration
            if(getSMTtrans()) {
                if(logic == LOGIC.NULL) {
                    logic=LOGIC.QF_BV;
                }
                if(encoding == ENCODING.NULL) {
                    encoding=ENCODING.NESTED;
                }
                
                if(smtsolver==SMTSOL.DEFAULT) {
                    //  Set SMT solver according to logic used. 
                    if(getUseBV()) {
                        smtsolver=SMTSOL.BOOLECTOR;
                    }
                    else if(getUseNIA() || getUseUF()) {
                        smtsolver=SMTSOL.Z3;
                    }
                    else {
                        assert getUseLIA() || getUseIDL();
                        smtsolver=SMTSOL.YICES2;
                    }
                }
                
                if(smtsolverpath==null && getRunSolver()) {
                    //  Set path to solver binary
                    if(smtsolver==SMTSOL.BOOLECTOR) {
                        if (boolectorpath == null) {
                            errorExit("Can't find Boolector: please specify -boolector-bin");
                        }
                        smtsolverpath = boolectorpath;
                    }
                    else if(smtsolver==SMTSOL.Z3) {
                        if (z3path == null) {
                            errorExit("Can't find Z3: please specify -z3-bin");
                        }
                        smtsolverpath=z3path;
                    }
                    else {
                        assert smtsolver==SMTSOL.YICES2;
                        if (yicespath == null) {
                            errorExit("Can't find Yices2: please specify -yices2-bin");
                        }
                        smtsolverpath=yicespath;
                    }
                }
                if(smtsolver==SMTSOL.BOOLECTOR && logic!=LOGIC.QF_BV) {
                    CmdFlags.warning("Attempting to use Boolector with logic other than QF_BV.");
                }
            }
            if(!getSMTtrans()) {
                //  Defensive setting logic and encoding to null. 
                logic=LOGIC.NULL;
                encoding=ENCODING.NULL;
            }
            if(getUseUF() && !getUseFlat()) {
                errorExit("SMT UF encoding must be flat, use with -smt-flat");
            }
            if(usingBoolector() && getSMTtrans()) {
                addSolverFlag("-m");
                addSolverFlag("--seed=" + smtseed);
            }
            if(getSMTtrans() && logic == LOGIC.QF_IDL) {
                aux_smt=true;   //  Must introduce auxiliary variables with IDL. 
                setUseCSE(false);
                setUseActiveCSE(false);
            }
        }
        else if(getMode()==ReadSolution || getMode()==ReadDomainStore) {
            // At the moment just for minion -- so did the user specify the minion file and the solution table file?
            if(CmdFlags.auxfile==null) {
                CmdFlags.cmdLineExit("When using ReadSolution mode, -out-aux must be used to specify the .aux file.");
            }
            
            if(CmdFlags.solutionfile == null) {
                CmdFlags.cmdLineExit("When using ReadSolution mode, -out-solution must be used to specify the name for the Essence Prime solution file(s).");
            }
            
            if(CmdFlags.minionsolfile==null) {
                CmdFlags.cmdLineExit("When using ReadSolution mode, -minion-sol-file must be used to specify the name of the Minion solution table file.");
            }
        }
        else {
            // What happened to the mode? Should be redundant, but doesn't hurt.
            assert false : "Mode not recognised" ;
        }
    }
    
    // from http://www.rgagnon.com/javadetails/java-0651.html
    public static String getPid() {
        String processName =
            java.lang.management.ManagementFactory.getRuntimeMXBean().getName();
        return processName.split("@")[0];
    }

}
