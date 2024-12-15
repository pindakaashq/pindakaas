package savilerow;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Felix Ulrich-Oltean, Peter Nightingale
    
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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import savilerow.expression.*;
import savilerow.model.Model;

// Implement the factor encoding of table constraints to achieve FPWC 
// when target solver applies GAC

public class FactorEncoding 
{
    private ArrayList<ASTNode> tableCons=new ArrayList<>();
    
    // This function interfaces between SR and the internal repn. 
    public void factorEncoding(Model m) {
        // Assume simplifiers have been run. 
        // Collect tables in top-level And.
        // Ignore a single table under Top. 
        
        ASTNode topand=m.constraints.getChild(0);
        
        if(!(topand instanceof And)) {
            return;
        }
        
        for(int i=0; i<topand.numChildren(); i++) {
            if(topand.getChild(i) instanceof Table) {
                tableCons.add(topand.getChild(i));
            }
        }
        
        if(tableCons.size()<2) {
            return;
        }
        
        //  Number variables. 
        
        int varcounter=0;
        HashMap<ASTNode, Integer> varNumber=new HashMap<>();
        HashMap<Integer, ASTNode> varFromNumber=new HashMap<>();
        
        //  Convert tables
        for(int i=0; i<tableCons.size(); i++) {
            ASTNode vars=tableCons.get(i).getChild(0);
            
            ArrayList<Integer> intvars=new ArrayList<Integer>(vars.numChildren()-1);
            
            for(int j=1; j<vars.numChildren(); j++) {
                if(!varNumber.containsKey(vars.getChild(j))) {
                    varcounter++;
                    varNumber.put(vars.getChild(j), varcounter);
                    varFromNumber.put(varcounter, vars.getChild(j));
                }
                intvars.add(varNumber.get(vars.getChild(j)));
            }
            
            ASTNode tab=tableCons.get(i).getChildConst(1);
            
            ArrayList<ArrayList<Integer>> inttab=new ArrayList<>(tab.numChildren()-1);
            
            for(int j=1; j<tab.numChildren(); j++) {
                ASTNode tuple=tab.getChildConst(j);
                ArrayList<Integer> row=new ArrayList<Integer>(tuple.getTupleLength());
                for(int k=1; k<=tuple.getTupleLength(); k++) {
                    row.add((int) tuple.getValueIdx(k));
                }
                inttab.add(row);
            }
            
            Constraint con=new Constraint(intvars, inttab);
            constraints.add(con);
            highestVarId = Math.max(highestVarId, Collections.max(con.varIds));
        }
        
        lastPrimaryVar=highestVarId;
        
        //System.out.println("Constraints at start");
        //System.out.print(printConstraints());
        createFactors();
        augmentConstraints();
        //System.out.println("Constraints at end of Factor Encoding");
        //System.out.print(printConstraints());
        
        if(CmdFlags.factor_encoding_mode>1) {
            //  Make new cts for the factor variables, remove original variables from scopes
            //  of original cts. 
            //System.out.println("Starting FDE");
            createFactorConstraints();
            filterOriginalScopes();
            //System.out.print(printConstraints());
            
            if(CmdFlags.factor_encoding_mode==3) {
                // One more pass of FDE
                resetState(m, varNumber, varFromNumber);
                
                createFactors();
                augmentConstraints();
                createFactorConstraints();
                filterOriginalScopes();
            }
            else if(CmdFlags.factor_encoding_mode==4) {
                filterScopesPlus();
            }
        }
        
        
        //  Make the new variables
        for(int i=0; i<factors.size(); i++) {
            int ub=factors.get(i).proj_table.size();
            ASTNode fac=m.global_symbols.newAuxiliaryVariable(0, ub);
            varNumber.put(fac, i+1+lastPrimaryVar);
            varFromNumber.put(i+1+lastPrimaryVar, fac);
        }
        
        //  Convert the constraints back to SR
        //  Delete the old constraints first.
        
        ASTNode replace=tableCons.get(0);
        for(int i=1; i<tableCons.size(); i++) {
            tableCons.get(i).getParent().setChild(tableCons.get(i).getChildNo(), new BooleanConstant(true));
        }
        
        ArrayList<ASTNode> replCons=new ArrayList<ASTNode>();
        
        for(int i=0; i<constraints.size(); i++) {
            ArrayList<Integer> vars=constraints.get(i).varIds;
            
            ArrayList<ASTNode> scp=new ArrayList<ASTNode>(vars.size());
            for(int j=0; j<vars.size(); j++) {
                scp.add(varFromNumber.get(vars.get(j)));
            }
            
            ArrayList<ArrayList<Integer>> tab=constraints.get(i).rows;
            
            ArrayList<ASTNode> tuples=new ArrayList<ASTNode>(tab.size());
            for(int j=0; j<tab.size(); j++) {
                ArrayList<ASTNode> tuple=new ArrayList<ASTNode>(tab.get(j).size());
                for(int k=0; k<tab.get(j).size(); k++) {
                    tuple.add(NumberConstant.make(tab.get(j).get(k)));
                }
                tuples.add(CompoundMatrix.make(tuple));
            }
            replCons.add(new Table(m, CompoundMatrix.make(scp), CompoundMatrix.make(tuples)));
        }
        
        replace.getParent().setChild(replace.getChildNo(), new And(replCons));
    }
    
    //  Convert factor variables into primary variables, update lastPrimaryVar,
    //  clear factors list. Effectively resets the state of this object.  
    //  This allows multiple passes of FDE. 
    void resetState(Model m, HashMap<ASTNode, Integer> varNumber, HashMap<Integer, ASTNode> varFromNumber) {
        //  Make the new variables
        for(int i=0; i<factors.size(); i++) {
            int ub=factors.get(i).proj_table.size();
            ASTNode fac=m.global_symbols.newAuxiliaryVariable(0, ub);
            varNumber.put(fac, i+1+lastPrimaryVar);
            varFromNumber.put(i+1+lastPrimaryVar, fac);
        }
        
        lastPrimaryVar+=factors.size();
        
        factors.clear();
    }
    
    private class Constraint {
        private ArrayList<Integer> varIds = new ArrayList<Integer>();
        private ArrayList<ArrayList<Integer>> rows = new ArrayList<ArrayList<Integer>>();
        public Constraint(int[][] table) {
            // the first row needs to specify the variable ids, starting with 0
            if (table.length < 2) throw new IllegalArgumentException(
                "Expecting a row of variable ids and some rows of supporting values");
            for (int v=0; v<table[0].length; v++)
                varIds.add(Integer.valueOf(table[0][v]));
            for (int r=1; r<table.length; r++){
                ArrayList<Integer> row = new ArrayList<Integer>(table[r].length);
                for (int c=0; c<table[r].length; c++) {
                    row.add(Integer.valueOf(table[r][c]));
                }
                rows.add(row);
            }
        }
        public Constraint(ArrayList<Integer> _varIds, ArrayList<ArrayList<Integer>> _rows) {
            varIds=_varIds;
            rows=_rows;
        }
        public int[][] getPrimitiveTable(){
            int numvars = varIds.size();
            int[][] table = new int[rows.size()+1][numvars];
            table[0] = varIds.stream().mapToInt(i -> i).toArray();
            for (int r =0; r<rows.size(); r++) {
                table[r+1] = rows.get(r).stream().mapToInt(i->i).toArray();
            }
            return table;
        }
    }

    // horrible hack, there must be a "proper" way
    public Constraint deepCopyOf(Constraint old) {
        // A constructor which makes a fresh copy of an existing Constraint object
        return new Constraint(old.getPrimitiveTable());
    }


    private class Factor {
        private TreeSet<Integer> scope;
        private TreeSet<Integer> constraint_idxs;
        private ArrayList<ArrayList <Integer>> proj_table;
        private int factor_ct=0;
        private Factor() {
            scope = new TreeSet<>();
            constraint_idxs = new TreeSet<>();
            proj_table = new ArrayList<>();
        }
    }


    private ArrayList<Constraint> constraints = new ArrayList<>();
    private ArrayList<Factor> factors = new ArrayList<>();
    private int highestVarId = 0;
    private int lastPrimaryVar = 0;
    
    /**
    Constructor for FactoredConstraints instances
    */
    /*public FactoredConstraints(int[][][] tables_in) {
        for (int c=0; c< tables_in.length; c++) {
            Constraint con = new Constraint(tables_in[c]);
            constraints.add(con);
            highestVarId = Math.max(highestVarId, Collections.max(con.varIds));
        }

    }*/
    
    /**
    Look through every combination of constraints
    */
    public void createFactors() {
        // consider all pairwise combinations of constraints
        for (int i=0; i<(constraints.size()-1); i++){
            for (int j=i+1; j<constraints.size(); j++){
                Constraint c1 = constraints.get(i);
                Constraint c2 = constraints.get(j);
                TreeSet<Integer> shared_vars = new TreeSet<Integer>();
                shared_vars.addAll(c1.varIds);
                shared_vars.retainAll(c2.varIds); // keep the intersection
                if (shared_vars.size() < 2) continue;
                // shall we make a new factor, or attach these constraints to an
                // existing factor instance?
                boolean is_new_factor = true;
                Set<Integer> relevant_cons = new HashSet<Integer>(
                    Arrays.asList(i,j)
                );
                for (Factor f : factors){
                    if (shared_vars.equals(f.scope)) {
                        is_new_factor = false;
                        f.constraint_idxs.addAll(relevant_cons);
                        break;
                    }
                }
                if (is_new_factor) {
                    Factor f = new Factor();
                    f.scope.addAll(shared_vars);
                    f.constraint_idxs.addAll(relevant_cons);
                    factors.add(f);
                }
            }
        }
    }
    
    /**    For each factor variable, visit the relevant constraints and insert new
    variable into constraint table, maintaining a projection of possible values
    */
    public void augmentConstraints() {
        for (Factor f : factors) {
            int newVarId = ++highestVarId;
            for (int cidx : f.constraint_idxs) {
                Constraint old_c = constraints.get(cidx);
                Constraint c = deepCopyOf(old_c); // a deep clone
                // go through each row and check whether we already have that combo in
                // our "projection"
                for (ArrayList<Integer> row : c.rows) {
                    ArrayList<Integer> proj_row = new ArrayList<Integer>();
                    for ( int var_id : f.scope) {
                        int var_pos_in_c = c.varIds.indexOf(Integer.valueOf(var_id));
                        proj_row.add(row.get(var_pos_in_c));
                    }
                    // the row index in the projection over this factor's variables
                    Integer prowid;
                    if (f.proj_table.contains(proj_row)) {
                        // we already have this combo in our projection
                        prowid = Integer.valueOf(f.proj_table.indexOf(proj_row));
                    } else {
                        prowid = f.proj_table.size();
                        f.proj_table.add(proj_row);
                    }
                    // we're adding on this variable's value (its projection row index) to
                    // the constraint's row
                    row.add(Integer.valueOf(prowid));
                }
                c.varIds.add(newVarId);
                // replace the old contraint with the augmented one
                constraints.set(cidx, c);
            }
        }
    }
    
    //   FDE functions
    void createFactorConstraints() {
        // For each factor, create a constraint linking it to the primary
        // variables and delete the relevant primary variables from the
        // scopes of the original cts. 
        for(int i=0; i<factors.size(); i++) {
            int factorvar=lastPrimaryVar+1+i;
            Factor f=factors.get(i);
            
            //  Scope is variables in factor, then the factor variable. 
            ArrayList<Integer> conVars=new ArrayList<Integer>(f.scope);
            conVars.add(factorvar);
            
            ArrayList<ArrayList<Integer>> conTab=new ArrayList<>();
            
            // Copy each tuple and add value of factor var at end.
            for(int j=0; j<f.proj_table.size(); j++) {
                
                ArrayList<Integer> tuple=new ArrayList<Integer>(f.proj_table.get(j));
                tuple.add(j);
                
                conTab.add(tuple);
            }
            
            constraints.add(new Constraint(conVars, conTab));
            f.factor_ct=constraints.size()-1;  //  Set index of factor constraint
        }
    }
    
    void filterOriginalScopes() {
        //  FDE -- for each new factor constraint, filter the
        // scopes of original constraints connected to the factor. 
        for(Factor f : factors) {
            for(int cid : f.constraint_idxs) {
                filterScope(constraints.get(cid), f.scope);
            }
        }
    }
    
    void filterScope(Constraint c, TreeSet<Integer> varsDelete) {
        //  Remove some variables from the scope of c and project the table.
        ArrayList<Boolean> idxRetain=new ArrayList<Boolean>(c.varIds.size());
        int rowsize=0;
        for(int i=0; i<c.varIds.size(); i++) {
            boolean toRetain=! (varsDelete.contains(c.varIds.get(i)));
            idxRetain.add(toRetain);
            if(toRetain) rowsize++;
        }
        
        for(int i=0; i<c.rows.size(); i++) {
            ArrayList<Integer> row=c.rows.get(i);
            ArrayList<Integer> replacementrow=new ArrayList<Integer>(rowsize);
            
            for(int j=0; j<row.size(); j++) {
                if(idxRetain.get(j)) {
                    replacementrow.add(row.get(j));
                }
            }
            
            c.rows.set(i, replacementrow);
        }
        
        ArrayList<Integer> newvarIds=new ArrayList<>();
        for(int j=0; j<c.varIds.size(); j++) {
            if(idxRetain.get(j)) {
                newvarIds.add(c.varIds.get(j));
            }
        }
        c.varIds=newvarIds;
    }
    
    void filterScopesPlus() {
        //  For each variable, suppose there is a graph where factors are 
        // the vertices, and two factors are connected by an edge if they are
        // in the same original constraint. 
        // For a connected component in this graph, the variable needs to be
        // in scope of a factor constraint only once. 
        
        //  Do one factor at a time, removing variables that are redundant
        for(int fidx=0; fidx<factors.size(); fidx++) {
            TreeSet<Integer> varsDelete=new TreeSet<>();
            
            for(int factvar : factors.get(fidx).scope) {
                if(checkConnected(fidx, factvar)) {
                    varsDelete.add(factvar);
                }
            }
            
            if(varsDelete.size()>0) {
                System.out.println("From factor "+fidx+" deleting variables:"+varsDelete);
                filterScope(constraints.get(factors.get(fidx).factor_ct), varsDelete);
            }
        }
    }
    
    boolean checkConnected(int fidx, int primaryvar) {
        // Is factor f connected to another factor with same primary variable in scope of its factor constraint?
        // If so then factor f can have primaryvar removed from its constraint
        
        TreeSet<Integer> visited=new TreeSet<>();
        ArrayList<Integer> frontier=new ArrayList<>();
        visited.add(fidx);
        frontier.add(fidx);
        
        while(frontier.size()>0) {
            int factorid=frontier.remove(frontier.size()-1);
            for(int ct : factors.get(factorid).constraint_idxs) {
                Constraint c=constraints.get(ct);
                
                //  Iterate for other factors in scope of c
                for(int v : c.varIds) {
                    if(v > lastPrimaryVar && ! visited.contains(v-lastPrimaryVar-1)) {
                        int fidx2=v-lastPrimaryVar-1;
                        Factor f2=factors.get(fidx2);
                        if(f2.scope.contains(primaryvar)) {
                            if( constraints.get(f2.factor_ct).varIds.indexOf(primaryvar)>-1 ) {
                                // constraint of the other factor contains the primary variable, so the constraint of f does not need to
                                // contain the primary variable. 
                                return true;
                            }
                            else {
                                // add fidx2 to frontier and continue search
                                visited.add(fidx2);
                                frontier.add(fidx2);
                            }
                        }
                    }
                }
            }
        }
        
        return false;
    }
    
    public String printConstraints() {
        String out = "";
        for (Constraint c : constraints) {
            out += "Constraint with variables:\n";
            out += c.varIds.stream().map(String::valueOf).collect(Collectors.joining(", "));
            out += "\n--- and values ---\n";
            for (ArrayList<Integer> row : c.rows) {
                out += row.stream().map(String::valueOf).collect(Collectors.joining(", "));
                out += "\n";
            }
        }
        return out;
    }

    public ArrayList<Constraint> getConstraints() {
        return this.constraints;
    }

    public int[][] getPrimitiveTableFor(int constraint_idx){
        return constraints.get(constraint_idx).getPrimitiveTable();
    }

    public ArrayList<Factor> getFactors() {
        return this.factors;
    }

    
    
}
