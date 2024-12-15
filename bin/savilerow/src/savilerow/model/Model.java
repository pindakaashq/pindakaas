package savilerow.model;
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

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Objects;

import savilerow.*;
import savilerow.expression.*;
import savilerow.treetransformer.*;

// Contains a CSP.

public class Model
{
    public ASTNode constraints;
    
    public SymbolTable global_symbols;
    
    public FilteredDomainStore filt;
    
    public ConstantMatrixStore cmstore;
    
    public ASTNode objective;
    
    public ASTNode branchingon;   // should be a 1-d matrix (or concatenate, or flatten..)
    
    public String heuristic;
    
    public ASTNode sns;   // Container for SNS related things
    
    public ASTNode preserveVariables;  //  Contains decision variables that are not to be deleted.
    
    public Sat satModel;
    
    public boolean subModelFlag=false;
    
    public ASTNode incumbentSolution;    // For optimisation using multiple solvers, intermediate solutions stored here. 
    
    //  Make an empty model to be populated using one of the setup methods.
    public Model() {
    }
    
    //  This one for construction in the parser.
    public void setup(ASTNode c, SymbolTable st, ASTNode ob, ASTNode branch, String h, ASTNode _sns, ASTNode _presvars)
    {
        assert c!=null;
        assert st!=null;
        
        constraints=c;
        global_symbols=st;
        st.m=this;
        objective=ob;
        branchingon=branch;
        heuristic=h;
        
        setDefaultBranchingOn();
        
        // Make a filt.
        filt=new FilteredDomainStore(global_symbols);
        cmstore=new ConstantMatrixStore(this);
        
        sns=_sns;
        preserveVariables=_presvars;
        // For dominance submodel
        subModelFlag = false;
    }
    
    public void setup(ASTNode c, SymbolTable st, FilteredDomainStore f, ConstantMatrixStore cm, ASTNode ob, ASTNode branch, String h, ASTNode _sns, ASTNode _presvars)
    {
        assert c!=null;
        assert st!=null;
        
        constraints=c;
        global_symbols=st;
        st.m=this;
        objective=ob;
        branchingon=branch;
        heuristic=h;
        
        setDefaultBranchingOn();
        
        filt=f;
        cmstore=cm;
        cm.m=this;
        
        sns=_sns;
        preserveVariables=_presvars;
    }
    
    private void setDefaultBranchingOn() {
        // Make a default branching on list if there isn't one.
        if(branchingon==null) {
            ArrayList<ASTNode> letgivs=new ArrayList<ASTNode>(global_symbols.lettings_givens);
            ArrayList<ASTNode> bran=new ArrayList<ASTNode>();
            for(int i=0; i<letgivs.size(); i++) {
                if(letgivs.get(i) instanceof Find) {
                    if(letgivs.get(i).getChild(1) instanceof MatrixDomain) {
                        bran.add(new Flatten(letgivs.get(i).getChild(0)));
                    }
                    else {
                        ArrayList<ASTNode> tmp=new ArrayList<ASTNode>();
                        tmp.add(letgivs.get(i).getChild(0));
                        bran.add(new CompoundMatrix(tmp));
                    }
                }
            }
            
            branchingon=new Cat(bran);
        }
    }
    
    // Simplify the model in-place.
    public void simplify()
    {
        //AuditTreeLinks atl=new AuditTreeLinks();
        TransformSimplify ts=new TransformSimplify();
        
        //atl.transform(constraints);
        boolean sat=global_symbols.simplify();   // return value -- true means no empty domains. 
        
        //  Constraints must go before objective, branching on because constraints may
        //  generate variable assignments, unification.
        if(!sat) {
            constraints=new Top(new BooleanConstant(false));
        }
        else {
            if(CmdFlags.getUseDeleteVars()) {
                TransformSimplifyExtended tse=new TransformSimplifyExtended(this);
                constraints=tse.transform(constraints);  // Does the extended one only on the constraints.
            }
            else {
                constraints=ts.transform(constraints);   
            }
        }
        
        if(objective!=null) {
            objective=ts.transform(objective);
            if(objective.getChild(0).isConstant()) {
                CmdFlags.println("Dropping objective: "+objective);
                objective=null;  // Throw away the objective if the expression inside has become a constant.
            }
        }
        if(branchingon!=null) {
            branchingon=ts.transform(branchingon);
        }
        if(preserveVariables!=null) {
            preserveVariables=ts.transform(preserveVariables);
        }
        
        // SNS related things
        if(sns!=null) {
            sns=ts.transform(sns);
        }
        
        filt.simplify();    //  Allows FilteredDomainStore to get rid of any assigned vars in its stored expressions.
    }
    
    // Substitute an expression throughout.
    // This is used to implement letting. 
    public void substitute(ASTNode toreplace, ASTNode replacement)
    {
        ReplaceASTNode t=new ReplaceASTNode(toreplace, replacement);
        constraints=t.transform(constraints);
        
        if(objective!=null)
            objective=t.transform(objective);
        
        if(branchingon!=null)
            branchingon=t.transform(branchingon);
        
        if(sns!=null) {
            sns=t.transform(sns);
        }
        
        global_symbols.substitute(toreplace, replacement);
    }
    
    public boolean typecheck() {
        
        // Branching on.
        if(branchingon!=null && branchingon.getDimension()!=1) {
            CmdFlags.println("ERROR: 'branching on' statement may only contain 1-dimensional matrices of decision variables.");
            return false;
        }
        
        //  Objective
        if(objective!=null) {
            if(!objective.typecheck(global_symbols)) return false;
            if(! (objective instanceof Maximising || objective instanceof Minimising) ) {
                CmdFlags.println("ERROR: Objective: "+objective);
                CmdFlags.println("ERROR: should be either minimising or maximising.");
                return false;
            }
            
            if( (!objective.getChild(0).isNumerical()) && (!objective.getChild(0).isRelation()) ) {
                CmdFlags.println("ERROR: Objective must be numerical or relational.");
                return false;
            }
        }
        
        if(sns!=null && !sns.typecheck(global_symbols)) return false;
        
        if(branchingon!=null && !branchingon.typecheck(global_symbols)) {
            return false;
        }
        if(!constraints.typecheck(global_symbols)) return false;
        if(!global_symbols.typecheck()) return false;
        if(!cmstore.typecheck()) return false;
        return true;
    }
    
    // Given a tree transformer, apply it to this model. 
    public boolean transform(TreeTransformer t) {
        if(CmdFlags.getVerbose()) {
            System.out.println("Rule:"+t.getClass().getName());
        }
        boolean changedModel=false;
        
        assert constraints instanceof Top;
        
        constraints=t.transform(constraints);
        changedModel=changedModel || t.changedTree;
        
        if(objective!=null) {
            objective=t.transform(objective);
            changedModel=changedModel || t.changedTree;
        }
        
        if(t.getContextCts()!=null) {
            // Extra constraints from the objective. 
            constraints.getChild(0).setParent(null); /// Do not copy all the constraints
            constraints=new Top(new And(constraints.getChild(0), t.getContextCts()));
            changedModel=true;
        }
        
        // WHY not domains??
        
        //  Branching on
        assert branchingon!=null;
        branchingon=t.transform(branchingon);
        changedModel=changedModel || t.changedTree;
        
        if(t.getContextCts()!=null) {
            // Extra constraints from branchingOn
            constraints.getChild(0).setParent(null); /// Do not copy all the constraints
            constraints=new Top(new And(constraints.getChild(0), t.getContextCts()));
            changedModel=true;
        }
        
        if(sns!=null) {
            sns=t.transform(sns);
            changedModel=changedModel || t.changedTree;
            if(t.getContextCts()!=null) {
                // Extra constraints from sns
                constraints.getChild(0).setParent(null); /// Do not copy all the constraints
                constraints=new Top(new And(constraints.getChild(0), t.getContextCts()));
                changedModel=true;
            }
        }
        
        if(preserveVariables!=null) {
            preserveVariables=t.transform(preserveVariables);
            changedModel=changedModel || t.changedTree;
        }
        
        if(CmdFlags.getVerbose() && changedModel) {
            System.out.println("Model has changed. Model after rule application:\n"+this.toString());
        }
        
        if(changedModel) {
            simplify();
            
            if(CmdFlags.getVerbose()) {
                System.out.println("Model after rule application and simplify:\n"+this.toString());
            }
        }
        
        assert constraints instanceof Top;
        return changedModel;
    }
    
    @Override
    public int hashCode() {
        return Objects.hash(constraints, global_symbols, filt, cmstore, objective, preserveVariables, branchingon, heuristic, incumbentSolution, sns);
    }
    
    @Override
    public boolean equals(Object b)
    {
        if(this.getClass() != b.getClass())
            return false;
        Model c=(Model)b;
        
        if(! c.constraints.equals(constraints))
            return false;
        if(! c.global_symbols.equals(global_symbols))
            return false;
        if(! c.filt.equals(filt))
            return false;
        if(! c.cmstore.equals(cmstore))
            return false;
        
        if( !(  objective==null ? c.objective==null : objective.equals(c.objective)))
            return false;
        if( !(  preserveVariables==null ? c.preserveVariables==null : preserveVariables.equals(c.preserveVariables)))
            return false;
        if(! branchingon.equals(c.branchingon))
            return false;
        if( !( heuristic==null ? c.heuristic==null : heuristic.equals(c.heuristic)))
            return false;
        if( !( incumbentSolution==null ? c.incumbentSolution==null : incumbentSolution.equals(c.incumbentSolution)))
            return false;
        if( !( sns==null ? c.sns==null : sns.equals(c.sns)))
            return false;
        
        return true;
    }
    
    public Model copy() {
        // Make an empty model to populate.
        Model newmodel=new Model();
        
        // Copy symbol table first.
        SymbolTable newst=global_symbols.copy(newmodel);
        FilteredDomainStore f=filt.copy(newst);
        //  Identifiers have a reference to the original symbol table. Fix it to point to the copy.
        TransformFixSTRef tf=new TransformFixSTRef(newmodel);
        
        ASTNode newct=tf.transform(constraints.copy());
        
        ASTNode ob=null;
        if(objective!=null) ob=tf.transform(objective.copy());
        
        ASTNode bran=tf.transform(branchingon.copy());
        
        ConstantMatrixStore cmst=cmstore.copy(newmodel);
        
        ASTNode snscopy=null;
        if(sns!=null) snscopy=tf.transform(sns.copy());
        
        ASTNode presvarscopy=null;
        if(preserveVariables!=null) presvarscopy=tf.transform(preserveVariables.copy());
        
        newmodel.setup(newct, newst, f, cmst, ob, bran, heuristic, snscopy, presvarscopy);
        
        if(incumbentSolution!=null) {
            newmodel.incumbentSolution=tf.transform(incumbentSolution.copy());
        }
        
        return newmodel;
    }
    
    // Filter out duplicate entries in the branching on list.
    void dedupBranchingOn() {
        assert branchingon instanceof CompoundMatrix || branchingon instanceof EmptyMatrix;
        ArrayList<ASTNode> ch=branchingon.getChildren(1);
        ArrayList<ASTNode> ch_out=new ArrayList<>();
        HashSet<ASTNode> seen=new HashSet<>();
        for(int i=0; i<ch.size(); i++) {
            ASTNode entry=ch.get(i);
            if(entry instanceof Negate) {
                entry=entry.getChild(0);
            }
            
            if(entry.getCategory()==ASTNode.Decision && !seen.contains(entry)) {
                seen.add(entry);
                ch_out.add(ch.get(i));
            }
        }
        branchingon=CompoundMatrix.make(ch_out);
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Output methods. 
    
    public void toMinion(BufferedWriter b, boolean propagate) throws IOException {
        toMinion(b, propagate, null);
    }
    
    // Output to minion
    public void toMinion(BufferedWriter b, boolean propagate, ArrayList<ASTNode> scope) throws IOException {
        if (!subModelFlag) {
            b.append("MINION 3\n");
        }
        for (String key : CmdFlags.stats.keySet()) {
            b.append("# "+key+" = "+CmdFlags.stats.get(key)+"\n");
        }
        
        b.append("**VARIABLES**\n");    
        global_symbols.toMinion(b);
        cmstore.toMinion(b);
        
        b.append("**SEARCH**\n");
        if(scope==null) {
            global_symbols.printPrintStmt(b);
        }
        else {
            b.append("PRINT [");
            for(int i=0; i<scope.size(); i++) {
                b.append("[");
                scope.get(i).toMinion(b, false);
                b.append("]");
                if(i<scope.size()-1) b.append(",");
            }
            b.append("]\n");
        }
        
        if(objective!=null) {
            objective.toMinion(b, false);
        }
        
        if(scope!=null) {
            b.append("VARORDER [");
            for(int i=0; i<scope.size(); i++) {
                scope.get(i).toMinion(b, false);
                //b.append(scope.get(i));
                if(i<scope.size()-1) b.append(",");
            }
            b.append("]\n");
        }
        
        if((!propagate) && scope==null && !subModelFlag) {
            // Prepare branchingon list.
            dedupBranchingOn();
            
            b.append("VARORDER ");
            if(heuristic!=null) {
                b.append(heuristic);
            }
            else {
                // default var ordering
                b.append("STATIC");
            }
            b.append(" ");
            
            branchingon.toMinion(b, false);
            b.append("\n");
            
            if(objective!=null) {
                // Does not necessarily optimise fully unless all variables are in a varorder stmt
                // Add a final VARORDER STATIC branching order. 
                b.append("VARORDER STATIC [");
                global_symbols.printAllVariables(b);
                b.append("]\n");
            }
        }
        
        b.append("**CONSTRAINTS**\n");
        constraints.toMinion(b, true);
        
        // SNS
        if(sns!=null) {
            sns.toMinion(b, false);
        }
        
        // AMO section
        if(CmdFlags.amo_detect_strong && propagate) {
            AMODetect.addAMOSection(b, this);
        }
        
        if (!subModelFlag) {
            b.append("**EOF**\n");
        }
    }
    
    // Output the model in Essence' eventually
    public String toString() {
        StringBuilder s=new StringBuilder();
        s.append("language ESSENCE' 1.0\n");
        s.append(global_symbols.toString());
        if(objective!=null) s.append(objective.toString());
        if(sns!=null) {
            s.append(sns.toString());
        }
        s.append("such that\n");
        s.append(constraints.toString());
        //s.append(filt.toString());
        return s.toString();
    }
    
    public void toFlatzinc(BufferedWriter b) throws IOException {
        if(CmdFlags.getGecodetrans()) {
            // get access to some predicates in gecode.
            b.append("predicate gecode_global_cardinality(array[int] of var int: x, array[int] of int: cover, array[int] of var int: counts);\n");
        }
        
        cmstore.toFlatzinc(b);
        global_symbols.toFlatzinc(b);
        
        constraints.toFlatzinc(b, true);
        
        generateFznSearch(b);
    }
    
    //  Is a variable classed as boolean for the fzn search annotation. 
    public boolean boolForFznSearch(ASTNode a) {
        return a.isRelation() && global_symbols.boolvar_bool.contains(a.toString());
    }
    
    private void generateFznSearch(BufferedWriter b) throws IOException {
        if(branchingon instanceof EmptyMatrix) {
            b.append("solve ");
            if(objective!=null) {
                objective.toFlatzinc(b, false);
            }
            else {
                b.append(" satisfy;\n");
            }
            return;
        }
        
        // Does branching-on list have both bool and int types?
        boolean branch_bool=false;
        boolean branch_int=false;
        
        for(int i=1; i<branchingon.numChildren() && !(branch_bool && branch_int); i++) {
            ASTNode a=branchingon.getChild(i);
            if(! a.isConstant()) {
                if(boolForFznSearch(branchingon.getChild(i))) {
                    branch_bool=true;
                }
                else {
                    branch_int=true;
                }
            }
        }
        
        ArrayList<ASTNode> branchNoConst=new ArrayList<>();
        for(int i=1; i<branchingon.numChildren(); i++) {
            ASTNode a=branchingon.getChild(i);
            if(! a.isConstant()) {
                branchNoConst.add(a);
            }
        }
        
        if(branch_bool && branch_int) {
            //  Build a sequence of search annotations. 
            b.append("solve :: seq_search([");
            
            int i=0;
            int n=branchNoConst.size();
            
            while(i<n) {
                boolean isbool=boolForFznSearch(branchNoConst.get(i));
                
                if(isbool) {
                    b.append("bool_search([");
                }
                else {
                    b.append("int_search([");
                }
                
                boolean firstInSeq=true;
                while(i<n && boolForFznSearch(branchNoConst.get(i))==isbool) {
                    if(!firstInSeq) {
                        b.append(", ");
                    }
                    branchNoConst.get(i).toFlatzinc(b, isbool);
                    i++;
                    firstInSeq=false;
                }
                b.append("], input_order, indomain_min, complete)");
                
                if(i<n) {
                    b.append(", ");
                }
            }
            
            b.append("]) ");
        }
        else {
            // One search annotation
            if(branch_bool) {
                b.append("solve :: bool_search([");
            }
            else {
                b.append("solve :: int_search([");
            }
            boolean firstInSeq=true;
            int i=0;
            int n=branchNoConst.size();
            while(i<n) {
                if(!firstInSeq) {
                    b.append(", ");
                }
                branchNoConst.get(i).toFlatzinc(b, branch_bool);
                i++;
                firstInSeq=false;
            }
            b.append("], input_order, indomain_min, complete) ");
        }
        
        if(objective!=null) {
            objective.toFlatzinc(b, false);
        }
        else {
            b.append("satisfy;\n");
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //  Minizinc output
    
    public void toMinizinc(StringBuilder b) {
        b.append("% Minizinc model produced by Savile Row from Essence Prime file "+CmdFlags.eprimefile);
        if(CmdFlags.paramfile!=null) b.append(" and parameter file "+CmdFlags.paramfile);
        b.append("\n");
        
        b.append("include \"globals.mzn\";\n");
        
        global_symbols.toMinizinc(b);
        cmstore.toMinizinc(b);
        constraints.toMinizinc(b, true);
        
        //  A search annotation with a static variable ordering. 
        b.append("solve :: int_search([");
        
        // Search order annotation. Should look at branchingon.
        global_symbols.printAllVariablesFlatzinc(b, ASTNode.Decision);
        
        b.append("], input_order, indomain_min, complete)\n");
        
        if(objective!=null) {
            objective.toMinizinc(b, false);
        }
        else {
            b.append(" satisfy;\n");
        }
    }
    
    public boolean setupSAT(HashSet<String> varsInConstraints) {
        try {
            if(!subModelFlag){
                if (CmdFlags.interactiveSolver){
                    satModel=new InteractiveSat(this);
                }
                else{
                    satModel=new Sat(this.global_symbols);
                }
            }
            satModel.generateVariableEncoding(varsInConstraints, CmdFlags.satoutputmapping);
            return true;
        }
        catch(IOException e) {
            // Tidy up. 
            File f = new File(CmdFlags.satfile);
            if (f.exists()) f.delete();
            return false;
        }
    }
    
    public boolean toSAT()
    {
        //  Clear global caches related to SAT output
        AMOPB.yCache.clear();
        
        try {
            constraints.toSAT(satModel);
            
            if(CmdFlags.getMaxsattrans() && objective!=null) {
                //  Encode the optimisation variable with soft clauses.
                objective.toSAT(satModel);
            }
            if(!CmdFlags.interactiveSolver){
                satModel.finaliseOutput();
            }
            return true;
        }
        catch(IOException e) {
            // Tidy up.
            File f = new File(CmdFlags.satfile);
            if (f.exists()) f.delete();
            return false;
        }
    }
    private long filesizeBak;
    //  Save and restore state, for dom rel mode.
    public void BTMark() throws IOException {
        //  Store file size so it can be truncated.
        RandomAccessFile f = new RandomAccessFile(CmdFlags.minionfile, "rws");
        filesizeBak = f.length();
        f.close();
    }
    public void BTMarkFZN() throws IOException {
        //  Store file size so it can be truncated.
        RandomAccessFile f = new RandomAccessFile(CmdFlags.fznfile, "rws");
        filesizeBak = f.length();
        f.close();
    }
    public void BTRestore() throws IOException {
        // Truncate the file.
        RandomAccessFile f = new RandomAccessFile(CmdFlags.minionfile, "rws");
        f.setLength(filesizeBak);
        f.close();
        
    }
    public void BTRestoreFZN() throws IOException {
        // Truncate the file.
        RandomAccessFile f = new RandomAccessFile(CmdFlags.fznfile, "rws");
        f.setLength(filesizeBak);
        f.close();
        
    }
    public void BTRemoveLastLine() throws IOException {
        // more robust erase last line method
        RandomAccessFile f = new RandomAccessFile(CmdFlags.minionfile, "rw");
        long length = f.length() - 1;
        byte b = -1;
        while(b != 10) {                     
            length--;
            f.seek(length);
            b = f.readByte();
        }
        length++;
        f.setLength(length);
        f.close();
    }

    public void BTRemoveLastLineFZN() throws IOException {
        // more robust erase last line method
        RandomAccessFile f = new RandomAccessFile(CmdFlags.fznfile, "rw");
        long length = f.length() - 1;
        byte b = -1;
        while(b != 10) {                     
            length--;
            f.seek(length);
            b = f.readByte();
        }
        length++;
        f.setLength(length);
        f.close();
    }
    /**
     * Hackiness explode for getting solver satisfy statement on fzn file
     * @return
     * @throws IOException
     */
    public String getSolverSatisfyForFZN() throws IOException {
        String ret = "";
        boolean flag = false;
        BufferedReader in = new BufferedReader(new FileReader(new File(CmdFlags.fznfile)));
        for (String x = in.readLine(); x != null; x = in.readLine()){
            if (x.startsWith("solve ::")){
                flag = true;
            }
            if (flag) {
                ret += x + "\n";
            }
        }
        return ret;
    }

    public void finaliseOutput(BufferedWriter out, FileOutputStream fw) throws IOException {
        out.flush();
        fw.getFD().sync();
        out.close(); 
    }
    public boolean toSMT() {
        try {
            constraints.toSMT((SMT)satModel);

            if (!subModelFlag){
                satModel.finaliseOutput();
            }
            return true;
        }
        catch(IOException e) {
            // Tidy up.
            File f = new File(CmdFlags.smtfile);
            if (f.exists()) f.delete();
            return false;
        }
    }

    public boolean setupSMT(HashSet<String> varsInConstraints) {
        try {
            if(!subModelFlag){
                if (CmdFlags.interactiveSolver){
                    satModel=new InteractiveSMT(this);
                }
                else{
                    satModel=new SMT(this.global_symbols);
                }
            }
            //Need to encode objective even if it doesn't appear in constraints
            if (this.objective != null) {
                if (CmdFlags.getUseBV()) {
                    this.global_symbols.markAsBitVector(((Identifier) this.objective.getChild(0)).getName());
                }
                else {
                    this.global_symbols.markAsInteger(((Identifier) this.objective.getChild(0)).getName());
                }
            }

            satModel.generateVariableEncoding(varsInConstraints, false);

            if (this.objective != null && CmdFlags.getSMTEncodeObjective()) {
                ((SMT)satModel).addObjective(this.objective);
            }
            return true;
        }
        catch(IOException e) {
            // Tidy up.
            File f = new File(CmdFlags.smtfile);
            if (f.exists()) f.delete();
            return false;
        }
    }
    
    //////////////////////////////////////////////////////////////////////////
    //  MIP output
    
    public void toMIP(BufferedWriter b) throws IOException {
        // LP format for CPLEX or Gurobi.
        if(objective!=null) {
            objective.toMIP(b);
        }
        else {
            b.append("Maximize\n");
            b.append("obj: 1\n");
        }
        
        b.append("Subject To\n");
        constraints.toMIP(b);
        
        b.append("Bounds\n");
        MIP.toMIPBounds(b, this);
        
        b.append("Generals\n");  //  Might need to be General for CPLEX
        MIP.toMIPGenerals(b, this);
        
        b.append("\nBinary\n");
        MIP.toMIPBinary(b, this);
        
        b.append("\nEnd\n");
    }
}
