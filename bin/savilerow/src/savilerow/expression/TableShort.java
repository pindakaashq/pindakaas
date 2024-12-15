package savilerow.expression;
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



import java.io.BufferedWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;

import savilerow.*;
import savilerow.model.*;

//  Short supports version of table constraint.
//  Table is a 3d ragged matrix i.e. a matrix of matrices of pairs.

public class TableShort extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    protected transient Model m;
    
    public TableShort(Model _m, ASTNode v, ASTNode tups) {
        super(v,tups);
        m=_m;
    }
    
    public boolean hasModel() {
        return true;
    }
    public Model getModel() {
        return m;
    }
    public void setModel(Model _m) {
        m=_m;
    }
    
	public ASTNode copy()
	{
	    return new TableShort(m, getChild(0), getChild(1));
	}
	public boolean isRelation(){return true;}
	public boolean strongProp() {
        return getChild(0).strongProp();
    }
	public boolean typecheck(SymbolTable st) {
	    if(!getChild(0).typecheck(st)) return false;
	    if(!getChild(1).typecheck(st)) return false;
	    
	    if(getChild(0).getDimension()!=1) {
            CmdFlags.println("ERROR: First argument of tableshort should be 1-dimensional matrix: "+this);
            return false;
        }
	    if(getChild(1).getDimension()!=3) {
	        CmdFlags.println("ERROR: Second argument of tableshort should be 3-dimensional matrix: "+this);
            return false;
	    }
	    if(getChild(1).getCategory()>ASTNode.Quantifier) {
	        CmdFlags.println("ERROR: Second argument of tableshort cannot contain decision variables: "+this);
            return false;
	    }
	    
        return true;
    }
    
    public ASTNode simplify() {
        ASTNode c0=getChildConst(0);
        if( (c0 instanceof CompoundMatrix || c0 instanceof EmptyMatrix) && (getChild(1).getCategory()==ASTNode.Constant)) {
            ASTNode table=getChildConst(1);
            
            if(getChild(1) instanceof CompoundMatrix || getChild(1) instanceof EmptyMatrix) {
                // Also of category constant, must be a matrix literal. 
                
                if(table instanceof EmptyMatrix) {
                    return new BooleanConstant(false);
                }
                if(table.getChild(1) instanceof EmptyMatrix) {
                    //  Contains an empty short support -- the constraint is entailed.
                    return new BooleanConstant(true);
                }
                
                // Make an identifier for it and store elsewhere.
                
                // Store table in deduplicated store.
                ASTNode tabid=m.cmstore.newConstantMatrixDedup(table);
                getChild(0).setParent(null);
                return new TableShort(m, getChild(0), tabid);
            }
            
            if(table instanceof CompoundMatrix || table instanceof EmptyMatrix) {
                // Both vars and table are matrix types we can work with. 
                if(table instanceof EmptyMatrix) {
                    // It's an empty vector of tuples, not a vector containing a single empty tuple. 
                    return new BooleanConstant(false);
                }
                if(table.getChild(1) instanceof EmptyMatrix) {
                    //  Contains an empty short support -- the constraint is entailed.
                    return new BooleanConstant(true);
                }
                
                if(c0 instanceof EmptyMatrix) {
                    // ... and table is non-empty
                    return new BooleanConstant(true);
                }
                
                if(c0.numChildren()==2) {
                    // Only one var in scope.  Convert the table to a set and the table constraint into an in.
                    if(c0==getChild(0)) {
                        c0.getChild(1).setParent(null);
                    }
                    ArrayList<ASTNode> values_ast=new ArrayList<>();
                    for(int i=1; i<table.numChildren(); i++) {
                        ASTNode tup=table.getChild(i);
                        
                        if(tup instanceof EmptyMatrix) {
                            //  Found an empty short tuple, constraint is always satisfied. 
                            return new BooleanConstant(true);
                        }
                        
                        assert tup instanceof CompoundMatrix && tup.numChildren()==2; // A short tuple with one pair in it. 
                        assert tup.getChild(1).getChild(1).getValue()==1;
                        
                        values_ast.add(tup.getChild(1).getChild(2));
                    }
                    
                    return new InSet(c0.getChild(1), new ToSet(new CompoundMatrix(values_ast)));
                }
                
                ArrayList<ASTNode> vars=c0.getChildren(1);
                
                // Project out assigned variables. Made more complicated by the table representation.
                int[] varmapping=new int[vars.size()];  
                int mapval=1;
                boolean allAssigned=true;
                for(int i=0; i<vars.size(); i++) {
                    if(vars.get(i).isConstant()) {
                        varmapping[i]=-1;
                        // Don't increment mapval. 
                    }
                    else {
                        varmapping[i]=mapval;
                        mapval++;
                        allAssigned=false;
                    }
                }
                
                // Select and project on assigned variables -- same as Table simplifier.
                if(varmapping[vars.size()-1]!=vars.size()) {
                    // Something is assigned. Filter the table, re-map variables.
                    HashSet<ASTNode> newtab=new HashSet<ASTNode>();
                    // Filter table into newtab.
                    for(int i=1; i<table.numChildren(); i++) {
                        ASTNode tup=table.getChild(i);
                        
                        boolean retain=true;
                        ArrayList<ASTNode> newtup=list();
                        tupleloop:
                        for(int j=1; j<tup.numChildren(); j++) {
                            int pair_var=(int) tup.getChild(j).getChild(1).getValue();
                            long pair_val=tup.getChild(j).getChild(2).getValue();
                            
                            if(varmapping[pair_var-1]==-1) {
                                if( pair_val != vars.get(pair_var-1).getValue()) {
                                    retain=false;
                                    break tupleloop;
                                }
                            }
                            else {
                                // var is mapped, val stays the same.
                                ASTNode newpair=CompoundMatrix.make(
                                    NumberConstant.make(varmapping[pair_var-1]), tup.getChild(j).getChild(2));
                                newtup.add(newpair);
                            }
                        }
                        
                        if(retain) {
                            if(newtup.size()==0) {
                                return new BooleanConstant(true);   //  Empty short support. 
                            }
                            newtab.add(CompoundMatrix.make(newtup));
                        }
                    }
                    
                    // filter vars
                    for(int i=vars.size()-1; i>=0; i--) {
                        if(vars.get(i).isConstant()) {
                            assert varmapping[i]==-1;
                            vars.remove(i);
                        }
                    }
                    ASTNode replacement_table=CompoundMatrix.make(new ArrayList<ASTNode>(newtab));
                    replacement_table=m.cmstore.newConstantMatrixDedup(replacement_table);
                    if(c0==getChild(0)) {
                        for(int i=0; i<vars.size(); i++) {
                            vars.get(i).setParent(null);
                        }
                    }
                    return new TableShort(m, CompoundMatrix.make(vars), replacement_table);
                }
                
                
                //  The extremely quick simplifier.
                /*if(allAssigned) {
                    // Iterate through the short tuples looking for one that is valid. 
                    for(int i=1; i<table.numChildren(); i++) {
                        ASTNode tup=table.getChild(i);
                        
                        boolean allSat=true;
                        for(int j=1; j<tup.numChildren(); j++) {
                            int pair_var=(int) tup.getChild(j).getChild(1).getValue();
                            long pair_val=tup.getChild(j).getChild(2).getValue();
                            
                            if(pair_val != vars.get(pair_var-1).getValue()) {
                                allSat=false;
                                break;
                            }
                        }
                        
                        if(allSat) {
                            // Found a support. 
                            return new BooleanConstant(true);
                        }
                    }
                    return new BooleanConstant(false);
                }*/
            }
        }
        return null;
    }
    
    static long shorttablecount=1;   //  Counter to get unique name for short tuple list in Minion output.
    
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    assert bool_context;
	    
	    if(getChild(1) instanceof CompoundMatrix || getChild(1) instanceof EmptyMatrix) {
	        ASTNode cmat=getChild(1);
	        
	        b.append("**SHORTTUPLELIST**\n");
            b.append("tableshort");
            b.append(String.valueOf(shorttablecount));
            
            b.append(" ");
            b.append(String.valueOf(cmat.numChildren()-1));
            b.append("\n");
            
            for(int i=1; i<cmat.numChildren(); i++) {
                b.append("[");
                ASTNode tup=cmat.getChild(i);
                for(int j=1; j<cmat.getChild(i).numChildren(); j++) {
                    long var=tup.getChild(j).getChild(1).getValue();
                    long val=tup.getChild(j).getChild(2).getValue();
                    b.append("(");
                    b.append(String.valueOf(var-1));    //  Minion indexes variables from 0, SR from 1.
                    b.append(",");
                    b.append(String.valueOf(val));
                    b.append("),");
                }
                b.append("]\n");
            }
            
            b.append("**CONSTRAINTS**\n");
	        b.append("shortstr2(");
            getChild(0).toMinion(b, false);
            b.append(", tableshort");
            b.append(String.valueOf(shorttablecount));
            b.append(")");
            
            shorttablecount++;
	    }
	    else {
	        // The table is an identifier
	        b.append("shortstr2(");
            getChild(0).toMinion(b, false);
            b.append(", ");
            getChild(1).toMinion(b, false);
            b.append(")");
	    }
	}
	
	
	public void toSAT(Sat satModel) throws IOException {
	    toSATHelper2(satModel);
	}
    public void toSATWithAuxVar(Sat satModel, long auxVar) throws IOException {
	    toSATHelper(satModel, auxVar);
	}
	
	////////////////////////////////////////////////////////////////////////////
	//
	//   First encoding of TableShort (for the reified case). Each tuple is represented with a SAT variable
	//   that is true iff the tuple is assigned. Then we have a disjunction of 
	//   these new SAT variables iff reification variable. 
	
	public void toSATHelper(Sat satModel, long auxVar) throws IOException {
        ASTNode tab=getChildConst(1);
        
        ArrayList<Long> newSatVars = new ArrayList<Long>(tab.numChildren());
        
        for (int i=1; i < tab.numChildren(); i++) {
            ASTNode tuple = tab.getChild(i);
            
            // One sat variable for each tuple. 
            long auxSatVar = satModel.createAuxSATVariable();
            
            ArrayList<Long> iffclause=new ArrayList<Long>(tuple.numChildren()-1);
            
            for (int j =1; j < tuple.numChildren(); j++) {
                long varidx=tuple.getChild(j).getChild(1).getValue();
                long value=tuple.getChild(j).getChild(2).getValue();
                
                long satLit=getChild(0).getChild((int)varidx).directEncode(satModel, value);
                
                iffclause.add(-satLit);
            }
            
            satModel.addClauseReified(iffclause, -auxSatVar);   // auxSatVar iff (lit1 /\ lit2 ...) <---> -auxSatVar iff (-lit1 \/ -lit2 ...)
            
            newSatVars.add(auxSatVar);
        }
        
        // Finally, the given auxVar is true iff one or more of newSatVars is true. 
        satModel.addClauseReified(newSatVars, auxVar);
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Second encoding of Table.
    //   Same as Bacchus except for final clause. 
    
    public void toSATHelper2(Sat satModel) throws IOException {
        ASTNode tab=getChildConst(1);
        
        int varcount = getChild(0).numChildren()-1;
        
        ArrayList<ASTNode> tups=tab.getChildren();
        
        ArrayList<ASTNode> vardoms=new ArrayList<ASTNode>();
        for(int i=1; i<=varcount; i++) {
            ASTNode var=getChild(0).getChild(i);
            if(var instanceof Identifier) {
                vardoms.add(((Identifier)var).getDomain());
            }
            else if(var.isConstant()) {
                vardoms.add(new IntegerDomain(new Range(var,var)));
            }
            else if(var instanceof SATLiteral) {
                vardoms.add(new BooleanDomainFull());
            }
            else {
                assert false : "Unknown type contained in tableshort constraint:"+var;
            }
        }
        
        ArrayList<Long> tupleSatVars = new ArrayList<Long>(tups.size());
        
        // Make a SAT variable for each tuple. 
        for(int i=1; i < tups.size(); i++) {
            // Filter out tuples that are not valid.
            boolean valid=true;
            ASTNode t = tups.get(i);
            int length = t.numChildren();
            for(int j = 1; j < length; ++j) {
              long var = t.getChild(j).getChild(1).getValue()-1;
              long val = t.getChild(j).getChild(2).getValue();
              if(!vardoms.get((int)var).containsValue(val)) {
                valid = false;
                break;
              }
            }
            
            if(!valid) {
                tups.set(i, tups.get(tups.size()-1));
                tups.remove(tups.size()-1);
                i--;
                continue;
            }
            
            //  Make a new sat variable for the tuple
            long newSatVar=satModel.createAuxSATVariable();
            tupleSatVars.add(newSatVar);
            
            // If command line flag, generate an iff to define the new sat variable.
            if(CmdFlags.short_tab_sat_extra) {
                ArrayList<Long> c=new ArrayList<Long>(tups.get(i).numChildren()-1);
                
                // Get the literals for this tuple into c. 
                for(int j=1; j<t.numChildren(); j++) {
                    ASTNode pair=t.getChild(j);
                    // System.out.print(pair);
                    c.add(-getChild(0).getChild((int) pair.getChild(1).getValue()).directEncode(satModel, pair.getChild(2).getValue()));
                }
                
                satModel.addClauseReified(c, -newSatVar);
            }
            
        }
        
        // Store for each variable, a list of its domain values
        ArrayList<ArrayList<Intpair>> vallist = new ArrayList<ArrayList<Intpair>>(varcount);
        // Store, for each variable, the tuples which implictly support it
        ArrayList<ArrayList<Long>> impclauselist = new ArrayList<ArrayList<Long>>(varcount);        
        // Store, for each literal, the tuples which explictly support it
        ArrayList<ArrayList<ArrayList<Long>>> expclauselist = new ArrayList<ArrayList<ArrayList<Long>>>(varcount);
        
        for(int var=1; var<=varcount; var++) {
            ASTNode varast=getChild(0).getChild(var);
            
            vallist.add(vardoms.get(var-1).getIntervalSet());
            impclauselist.add(new ArrayList<Long>());
            expclauselist.add(new ArrayList<ArrayList<Long>>((int)Intpair.numValues(vallist.get(var-1))));
            for(int j = 0; j < Intpair.numValues(vallist.get(var-1)); ++j) {
                expclauselist.get(var-1).add(new ArrayList<Long>());
            }
        }
        
        for(int tup=1; tup < tups.size(); tup++) {
            ASTNode t = tups.get(tup);
            int length = t.numChildren();
            // Track used variables
            ArrayList<Boolean> used_vars = new ArrayList<Boolean>(Collections.nCopies(varcount, false));
            for(int j = 1; j < length; ++j) {
                int var = (int)(t.getChild(j).getChild(1).getValue() - 1);
                long val = t.getChild(j).getChild(2).getValue();
                assert used_vars.get(var) == false;
                used_vars.set(var, true);
                int loc = (int) Intpair.location(vallist.get(var), val);
                assert loc != -1;
                expclauselist.get(var).get(loc).add(tupleSatVars.get(tup-1));
            }
            
            for(int j = 0; j < varcount; ++j)
            {
                if(used_vars.get(j) == false) {
                    impclauselist.get(j).add(tupleSatVars.get(tup-1));
                }
            }
        }
        
        // Now generate and post clauses
        for(int i = 0; i < varcount; ++i) {
            ASTNode varast=getChild(0).getChild(i+1);
            for(int val = 0; val < Intpair.numValues(vallist.get(i)); ++val)
            {
                // firstly, for all explicit clauses, ~lit -> ~clause ( lit \/ ~clause )
                if(!CmdFlags.short_tab_sat_extra) {
                    for(int clause = 0; clause < expclauselist.get(i).get(val).size(); ++clause) {
                        long lit = varast.directEncode(satModel, Intpair.lookup(vallist.get(i),val));
                        
                        satModel.addClause(lit, -expclauselist.get(i).get(val).get(clause));
                    }
                }
                
                // Secondly, for all implicit + explicit clauses for lit,
                // ~(/\clauses) -> ~lit ( ~lit \/ expclause1 \/ ... \/ expclausen \/ impclause1 \/ ... impclausen)
                ArrayList<Long> buf=new ArrayList<Long>(1+expclauselist.get(i).get(val).size()+impclauselist.get(i).size());
                
                buf.add(-varast.directEncode(satModel, Intpair.lookup(vallist.get(i), val)));
                
                for(int clause = 0; clause < expclauselist.get(i).get(val).size(); ++clause)
                {
                    buf.add(expclauselist.get(i).get(val).get(clause));
                }
                for(int clause = 0; clause < impclauselist.get(i).size(); ++clause)
                {
                    buf.add(impclauselist.get(i).get(clause));
                }
                satModel.addClause(buf);
            }
        }
        
        satModel.addClause(tupleSatVars);   // One of the tuples must be assigned -- redundant but probably won't hurt.
    }
    
    // Following cut n pasted from TransformMakeTable.java
    //   Assumes only decision variables and references to the constant matrices remain.
    public ArrayList<ASTNode> getVariables(ASTNode exp) {
        HashSet<ASTNode> tmp=new HashSet<ASTNode>();
        getVariablesInner(exp, tmp);
        return new ArrayList<ASTNode>(tmp);
    }
    
    private void getVariablesInner(ASTNode exp, HashSet<ASTNode> varset) {
        if(exp instanceof Identifier && exp.getCategory()>ASTNode.Constant) {
            // Collect all identifiers except those that refer to a constant matrix.
            varset.add(exp);
        }
        else {
            for(int i=0; i<exp.numChildren(); i++) {
                getVariablesInner(exp.getChild(i), varset);
            }
        }
    }
    
    public String toString() {
        return "tableshort("+getChild(0)+", "+getChild(1)+")";
    }
}
