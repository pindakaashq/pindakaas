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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import savilerow.expression.*;
import savilerow.model.Model;
import savilerow.treetransformer.TransformQuantifiedExpression;

// Contains all tabulation methods
// Has a common instance of TabulationUtils shared by all tabulation methods. 

public class Tabulation 
{
    public static final String ANSI_RESET  = "\u001B[0m";
    public static final String ANSI_RED    = "\u001B[31m";
    public static final String ANSI_GREEN  = "\u001B[32m";
    
    private static boolean verbose=false;
    
    private Model m;
    
    private TabulationUtils tu;
    
    private long nodelimit;
    
    public Tabulation(Model _m) {
        m=_m;
        tu=new TabulationUtils(m);
        nodelimit=CmdFlags.tabulate_nolimit ? Long.MAX_VALUE : 300000;
    }
    
    public void process(boolean prop) {
        //  First, MakeTable functions.
        processMakeTable(m.constraints);
        
        if(!prop) {
            
            if(CmdFlags.make_short_tab==3 || CmdFlags.make_short_tab==4) {
                //  Tabulation of constraints. 
                //  First find sets of constraints with the same scope, attempt
                //  tabulation of the conjunction of them.
                HashMap<ArrayList<ASTNode>, ArrayList<ASTNode>> scopeslist=buildScopesList(m.constraints);
                identicalScopes(m.constraints, scopeslist);
                
                //  The other three heuristics -- applied to each top-level constraint
                applyHeuristicsBool(m.constraints);
            }
            
            if(CmdFlags.tabulate_opt && m.objective!=null) {
                tabulateObjective();
                
                //  Bit of a hack -- remove the redundant variables 
                RemoveRedundantVars rrv=new RemoveRedundantVars();
                rrv.transform(m);
            }
            
            if(CmdFlags.tabulate2) {
                double tabstarttime=System.currentTimeMillis();
                
                //  New tabulation -- can extract boolean subexpressions 
                //  as well as numerical subexpressions. 
                
                // Always use long tables -- for now.
                int tmp=CmdFlags.make_short_tab;
                CmdFlags.make_short_tab=1;
                
                //  Identical scopes works as previously. 
                HashMap<ArrayList<ASTNode>, ArrayList<ASTNode>> scopeslist=buildScopesList(m.constraints);
                identicalScopes(m.constraints, scopeslist);
                
                //  Apply heuristics to top-level constraints and boolean subexpressions.
                //  Also do a variation of identical scopes where a boolean subexpression has an
                //  identical scope to a top-level ct. 
                applyHeuristicsBool2(m.constraints, scopeslist);
                
                applyHeuristicsNumerical2(m.constraints, scopeslist);
                
                CmdFlags.make_short_tab=tmp;
                
                CmdFlags.tabtime=(((double) System.currentTimeMillis() - tabstarttime) / 1000.0);  // Record the time taken for tabulation. 
            }
        }
    }
    
    //////////////////////////////////////////////////////////////////////////
    //  Deal with MakeTable functions
    //  Top-down descent of tree. 
    private void processMakeTable(ASTNode curnode) {
        if(curnode instanceof MakeTable) {
            if(CmdFlags.make_short_tab==0) {
	            //  Option 0 given on command line. 
	            //  Remove the MakeTable function
	            ASTNode parent=curnode.getParent();
	            int idx=curnode.getChildNo();
	            curnode.getChild(0).setParent(null);
	            parent.setChild(idx, curnode.getChild(0));
	            
	            //  Recursively process the replacement ASTNode. 
	            processMakeTable(parent.getChild(idx));
	        }
	        else {
	            //  Tabulate with no limits. Always returns a table constraint. 
                ASTNode newTable=tabulate(curnode.getChild(0), Long.MAX_VALUE, (CmdFlags.make_short_tab==2 || CmdFlags.make_short_tab==4), "MakeTableFunction");
	            
                curnode.getParent().setChild(curnode.getChildNo(), newTable);
            }
        }
        else if(curnode instanceof Table) {
            //  Check the table.
            int r=curnode.getChild(0).numChildren()-1;
            ASTNode tab=curnode.getChildConst(1);
            if(tab.numChildren()>1) {
                if(tab.getChild(1).getTupleLength()!=r) {
                    CmdFlags.errorExit("Table scope size does not match length of tuples.\n"+curnode);
                }
                if(!tab.isRegularMatrix()) {
                    CmdFlags.errorExit("Table constraint contains irregular matrix (i.e. length of tuples differs).\n"+curnode);
                }
            }
        }
        else {
            //  Recursive descent of the tree
            for(int i=0; i<curnode.numChildren(); i++) {
                processMakeTable(curnode.getChild(i));
            }
        }
    }
    
    //////////////////////////////////////////////////////////////////////////
    //  Identical scopes heuristic
    
    private void identicalScopes(ASTNode top, HashMap<ArrayList<ASTNode>, ArrayList<ASTNode>> scopeslist) {
        //  Find entries in scopeslist where number of constraints > 1
        
        for(Map.Entry<ArrayList<ASTNode>,ArrayList<ASTNode>> p : scopeslist.entrySet()) {
            ArrayList<ASTNode> ctlist=p.getValue();
            if(ctlist.size()>1) {
                ASTNode totabulate=new And(ctlist);
                
                if(verbose) {
                    System.out.println("H4");
                    System.out.println("Trying ct:"+totabulate);
                }
                
                ASTNode newTable=tabulate(totabulate, nodelimit, (CmdFlags.make_short_tab==2 || CmdFlags.make_short_tab==4), "IdenticalScopes");
                
                if(newTable!=null) {
                    replaceConstraintSet(ctlist, newTable);
                    // Update scopeslist
                    ctlist.clear();
                    ctlist.add(newTable);
                }
            }
        }
    }
    
    // Collect scopes of top-level constraints. 
    private HashMap<ArrayList<ASTNode>, ArrayList<ASTNode>> buildScopesList(ASTNode top) {
        HashMap<ArrayList<ASTNode>, ArrayList<ASTNode>> scopeslist=new HashMap<>();
        
        // Populate scopeslist
        if(top.getChild(0) instanceof And) {
            ASTNode a=top.getChild(0);
            for(int i=0; i<a.numChildren(); i++) {
                ASTNode ct=a.getChild(i);
                if(!(ct instanceof Table) && !(ct instanceof TableShort) && !(ct instanceof NegativeTable)
                    && !(ct instanceof Tag)) {
                    assert ct.isRelation();
                    
                    // Get the scope. 
                    ArrayList<ASTNode> scope=TabulationUtils.getVariablesOrdered(ct);
                    ASTNode.sortByAlpha(scope);  //  Sort alphabetically
                    
                    if(! scopeslist.containsKey(scope)) {
                        scopeslist.put(scope, new ArrayList<ASTNode>());
                    }
                    
                    scopeslist.get(scope).add(ct);
                }
            }
        }
        
        return scopeslist;
    }
    
    //  This version finds sets of constraints with scope of one constraint containing the others
    //  Arbitrary choice of 90% of variables of the outermost constraint must be in the other cts to be a candidate. 
   /* private void overlappingScopes(ASTNode top) {
        //  First map variables to constraints containing them
        
        HashMap<ASTNode, ArrayList<Integer>> varToCons=new HashMap<>();
        ArrayList<ASTNode> constraints=new ArrayList<>();
        ArrayList<ArrayList<ASTNode>> scopes=new ArrayList<>();
        ArrayList<HashSet<ASTNode>> scopesets=new ArrayList<>();
        
        ArrayList<Boolean> included=new ArrayList<Boolean>();
        
        // Populate varToCons etc. 
        if(top.getChild(0) instanceof And) {
            ASTNode a=top.getChild(0);
            for(int i=0; i<a.numChildren(); i++) {
                ASTNode ct=a.getChild(i);
                if(!(ct instanceof Table) && !(ct instanceof TableShort) && !(ct instanceof NegativeTable)
                    && !(ct instanceof Tag)) {
                    int ctid=constraints.size();
                    
                    assert ct.isRelation();
                    
                    // Get the scope. 
                    ArrayList<ASTNode> scope=TabulationUtils.getVariablesOrdered(ct);
                    ASTNode.sortByAlpha(scope);  //  Sort alphabetically
                    
                    for(int j=0; j<scope.size(); j++) {
                        if(!varInConstraints.contains(scope.get(j))) {
                            varToCons.put(scope.get(j), new ArrayList<ASTNode>());
                        }
                        varToCons.get(scope.get(j)).add(ctid);
                    }
                    
                    constraints.add(ct);
                    scopes.add(scope);
                    scopesets.add(new HashSet(scope));
                    included.add(false);
                }
            }
        }
        
        // Find the 'outermost' constraints, which have 90% of their variables
        // covered by other constraints with scopes that are a non-strict subset. 
        // Where two constraints have the same scope, the first one (lower index) is preferred
        
        ArrayList<ASTNode> outer=new ArrayList<ASTNode>();
        
        for(int i=0; i<constraints.size(); i++) {
            ArrayList<ASTNode> scp=scopes.get(i);
            int covered_vars=0;
            
            ArrayList<Integer> subcts=new ArrayList<Integer>();
            
            for(int j=0; j<scp.size(); j++) {
                ArrayList<Integer> potentialCts=varToCons.get(scp.get(j));
                
                for(int k=0; k<potentialCts.size(); k++) {
                    int c2=potentialCts.get(k);
                    // check if c2 scope is a subset of the constraint's scope.
                    
                }
                
                
                
            }
            
            
            
            
            
        }
        
    }*/
    
    private void replaceConstraintSet(ArrayList<ASTNode> ctlist, ASTNode replacement) {
        ASTNode a=ctlist.get(0);
        
        a.getParent().setChild(a.getChildNo(), replacement);
        
        //  Clear the rest of the constraints.
        for(int i=1; i<ctlist.size(); i++) {
            a=ctlist.get(i);
            a.getParent().setChild(a.getChildNo(), new BooleanConstant(true));
        }
    }
    
    /////////////////////////////////////////////////////////////////////////
    //  Three single-constraint heuristics
    
    private void applyHeuristicsBool(ASTNode top) {
        //  Simply iterate through the top-level constraints. 
        
        if(top.getChild(0) instanceof And) {
            ASTNode a=top.getChild(0);
            for(int i=0; i<a.numChildren(); i++) {
                ASTNode curnode=a.getChild(i);
                //  Checks are a bit paranoid, not all are necessary
                if(!(curnode instanceof And) && curnode.isRelation()
                    && !(curnode instanceof Table) && !(curnode instanceof TableShort) && !(curnode instanceof NegativeTable)
                    && !(curnode instanceof BooleanConstant)) {
                    //   Heuristics for applying the (short) table converter. 
                    //   Only applied in final tailoring process.
                    //   Top-level constraints only.  Boolean expressions nested within top-level constraints are not tabulated.  
                    String h=heuristic(curnode);
                    if(h!=null) {
                        ASTNode newTable=tabulate(curnode, nodelimit, (CmdFlags.make_short_tab==2 || CmdFlags.make_short_tab==4), h);
                        
                        if(newTable!=null) {
                            a.setChild(i, newTable);
                        }
                    }
                }
            }
        }
    }
    
    /////////////////////////////////////////////////////////////////////////
    //  Second version that can tabulate subexpressions as well as top-level
    //  cts.
    private void applyHeuristicsBool2(ASTNode top, HashMap<ArrayList<ASTNode>, ArrayList<ASTNode>> scopeslist) {
        //  Breadth-first search in AST. 
        
        if(top.getChild(0) instanceof And) {
            ASTNode a=top.getChild(0);
            
            ArrayDeque<ASTNode> deque=new ArrayDeque<>(a.getChildren());
            
            while(!deque.isEmpty()) {
                ASTNode curnode=deque.poll();
                
                //  Gecode and Minion support reified table so it's safe
                //  Chuffed and std flatzinc do not, and the reified table is
                //  expanded into a full-length table constraint with the reification var. 
                //  Sat encoding of reified table is weak.
                //  Apply product of domain size limit to chuffed+std flatzinc. 
                
                //  First check for identical scope with a top-level constraint
                //  (when curnode is not top-level)
                if(curnode.isRelation() && curnode.getDimension()==0
                    && !(curnode instanceof Table) && !(curnode instanceof TableShort) && !(curnode instanceof NegativeTable)
                    && !(curnode instanceof BooleanConstant)
                    && !curnode.getParent().inTopAnd()) {
                    
                    // Get the scope. 
                    ArrayList<ASTNode> scope=TabulationUtils.getVariablesOrdered(curnode);
                    ASTNode.sortByAlpha(scope);  //  Sort alphabetically
                    //  Check if there is a top-level with the same scope
                    //  and either there is more than one such top-level constraint, or
                    //  it does not contain curnode. 
                    if(scopeslist.containsKey(scope) && (scopeslist.get(scope).size()>1 || !contains(scopeslist.get(scope).get(0), curnode)) ) {
                        ASTNode toplevelcts=new And(scopeslist.get(scope));
                        
                        if(applyHeuristicsBool2Attempt(curnode, toplevelcts, "IdenticalScopesNested")) {
                            continue;
                        }
                    }
                }
                
                //  Check it's a candidate, then apply the three heuristics. 
                if(curnode.isRelation() && curnode.getDimension()==0
                    && !(curnode instanceof Table) && !(curnode instanceof TableShort) && !(curnode instanceof NegativeTable)
                    && !(curnode instanceof BooleanConstant)) {
                    String h=heuristic(curnode);
                    if(h!=null) {
                        if(applyHeuristicsBool2Attempt(curnode, null, curnode.getParent().inTopAnd()?h:(h+"Nested"))) {
                            continue;
                        }
                    }
                }
                
                //if(!(curnode.isRelation() && curnode.getDimension()==0) || !curnode.strongProp()) {
                    //  StrongProp check is an optimisation -- don't look into 
                    //  constraints that are already expected to get GAC. 
                    //  Unfortunately drops the 'identical scopes' heuristic. 
                    deque.addAll(curnode.getChildren());
                //}
            }
        }
    }
    
    //  When a bool heuristic fires, attempt tabulation either in place or extracted to a 
    //  variable (if not top-level, and not using Gecode or Minion). 
    
    private boolean applyHeuristicsBool2Attempt(ASTNode curnode, ASTNode context, String heuristic) {
        //  If targeting Minion or Gecode, reified table is supported so always do it in place with ordinary limit.
        //  Else, apply an extra limit because it will be extracted then full d^n table generated. 
        
        if(!CmdFlags.getMiniontrans() && !CmdFlags.getGecodetrans() && !CmdFlags.getSattrans() && !curnode.getParent().inTopAnd()) {
            // Not top-level, and solver does not support reified table. 
            // Limit product of domains. 
            ArrayList<ASTNode> scope=TabulationUtils.getVariablesOrdered(curnode);
            double domprod=1.0;
            for(int i=0; i<scope.size(); i++) {
                domprod=domprod*Intpair.numValues(scope.get(i).getIntervalSetExp());
            }
            if(domprod>((double)nodelimit)) {
                return false;
            }
        }
        //  Attempt tabulation in-place
        //  Very conservative -- make sure everything is copied. 
        ASTNode totab=curnode.copy();
        if(context!=null) {
            totab=new And(context.copy(), totab);
        }
        
        ASTNode newTable=tabulate(totab, nodelimit, false, heuristic);
        
        if(newTable!=null) {
            //   Replace. 
            curnode.getParent().setChild(curnode.getChildNo(), newTable);
            return true;
        }
        
        return false;
    }
    
    /////////////////////////////////////////////////////////////////////////
    //  Numerical expressions
    
    private void applyHeuristicsNumerical2(ASTNode top, HashMap<ArrayList<ASTNode>, ArrayList<ASTNode>> scopeslist) {
        //  Iterate through every numerical decision expression 
        ArrayList<ASTNode> newCts=new ArrayList<>();
        
        //  Cache mapping numerical expressions that have already been tabulated to aux variables
        HashMap<ASTNode, ASTNode> auxcache=new HashMap<>();
        
        if(top.getChild(0) instanceof And) {
            ASTNode a=top.getChild(0);
            
            for(int i=0; i<a.numChildren(); i++) {
                ASTNode outer_ct=a.getChild(i);
                
                //  Find numerical expressions inside outer_ct, looking inside containers if necessary
                ArrayDeque<ASTNode> deque=new ArrayDeque<>(outer_ct.getChildren());
                
                while(!deque.isEmpty()) {
                    ASTNode curnode=deque.poll();
                    
                    //  If curnode is a numerical expression, and it will be extracted by
                    //  general flattening, then it's a candidate for tabulation.
                    ASTNode par=curnode.getParent();
                    if(curnode.isNumerical() 
                        && !(curnode instanceof Identifier)
                        && !(curnode instanceof NumberConstant)
                        && !(curnode instanceof Mapping)
                        && curnode.getDimension()==0 
                        && curnode.toFlatten(false)
                        && !(par instanceof ToVariable || par instanceof Equals)
                        ) {
                        
                        //  First check the cache -- have we already tabulated this numerical expression?
                        //  If so, use the aux variable we already made. 
                        if(auxcache.containsKey(curnode)) {
                            curnode.getParent().setChild(curnode.getChildNo(), auxcache.get(curnode));
                            continue;  //  Continue the while loop. 
                        }
                        
                        // Trial auxiliary variable and constraint. 
                        //System.out.println("Trying numerical expression:"+curnode);
                        ASTNode tmpaux=m.global_symbols.newAuxHelper(curnode);
                        ASTNode ct=new Equals(curnode.copy(), tmpaux);
                        
                        //  First do identical scopes heuristic. 
                        
                        ArrayList<ASTNode> scope=TabulationUtils.getVariablesOrdered(curnode);
                        ASTNode.sortByAlpha(scope);  //  Sort alphabetically
                        
                        //  Check if there is a top-level with the same scope
                        //  and either there is more than one such top-level constraint, or
                        //  it does not contain curnode. 
                        if(scopeslist.containsKey(scope) && (scopeslist.get(scope).size()>1 || !contains(scopeslist.get(scope).get(0), curnode)) ) {
                            ASTNode toplevelcts=new And(scopeslist.get(scope));
                            ASTNode newTable=tabulate(new And(ct, toplevelcts), nodelimit, false, "IdenticalScopesNestedNum");
                            
                            if(newTable!=null) {
                                newCts.add(newTable);
                                
                                //  Replace the numerical expression with the aux variable. 
                                curnode.getParent().setChild(curnode.getChildNo(), tmpaux);
                                
                                // Add to cache
                                auxcache.put(curnode, tmpaux);
                                continue;  // Continue looping through the queue. 
                            }
                        }
                        
                        // Temporarily replace curnode with tmpaux so that calling strongProp on outer_ct produces the appropriate answer. 
                        ASTNode p=curnode.getParent();
                        p.setChild(curnode.getChildNo(), tmpaux);
                        boolean outer_ct_strong=outer_ct.strongProp();
                        // Restore
                        curnode.setParent(null);
                        p.setChild(curnode.getChildNo(), curnode);
                        
                        //  Special case of strong prop heuristic, plus other two heuristics. 
                        boolean stprop=outer_ct_strong && !ct.strongProp();
                        String h=heuristic(ct);
                        if(stprop || h!=null) {
                            ASTNode newTable=tabulate(ct, nodelimit, false, stprop?"WeakPropagation1NestedNum":h+"NestedNum");
                            
                            if(newTable!=null) {
                                newCts.add(newTable);
                                
                                //  Replace the numerical expression with the aux variable. 
                                curnode.getParent().setChild(curnode.getChildNo(), tmpaux);
                                
                                // Add to cache
                                auxcache.put(curnode, tmpaux);
                                
                                // Continue the loop
                                continue;
                            }
                        }
                        
                        //  Tidy up by deleting the auxiliary variable. 
                        m.global_symbols.deleteSymbol(tmpaux.toString());
                    }
                    
                    //  Put children into the queue. 
                    deque.addAll(curnode.getChildren());
                }
            }
            // Add the new constraints at the top level. 
            top.getChild(0).setParent(null);
            top.setChild(0, new And(top.getChild(0), new And(newCts)));
        }
    }
    
    //////////////////////////////////////////////////////////////////////////
    //
    //  Tabulate components of a sum objective function
    
    ASTNode optVar;
    
    ASTNode optCt=null;
    
    ArrayList<ASTNode> optTerms;
    boolean[] optTermsPolarity;
    
    HashMap<ASTNode, ArrayList<ASTNode>> idToCons=new HashMap<>();  // Collect constraints containing each identifier. 
    
    private boolean min;
    
    private void tabulateObjective() {
        min=(m.objective instanceof Minimising);
        optVar=m.objective.getChild(0);
        findOptCt(m.constraints);
        System.out.println("In tabulateObjective, optimisation constraint:"+optCt);
        
        ASTNode wsum;
        
        if( (optCt instanceof ToVariable && optCt.getChild(1).equals(optVar) && optCt.getChild(0) instanceof WeightedSum)
            || (optCt instanceof Equals && optCt.getChild(1).equals(optVar) && optCt.getChild(0) instanceof WeightedSum)
            || (optCt instanceof Equals && optCt.getChild(0).equals(optVar) && optCt.getChild(1) instanceof WeightedSum)
            || (optCt instanceof LessEqual && optCt.getChild(1).equals(optVar) && optCt.getChild(0) instanceof WeightedSum && min) 
            || (optCt instanceof LessEqual && optCt.getChild(0).equals(optVar) && optCt.getChild(1) instanceof WeightedSum && !min) ) {
            
            if(optCt.getChild(0) instanceof WeightedSum) {
                wsum=optCt.getChild(0);
            }
            else {
                wsum=optCt.getChild(1);
            }
            optTerms=wsum.getChildren();
            
            optTermsPolarity=new boolean[optTerms.size()];
            for(int i=0; i<optTerms.size(); i++) {
                optTermsPolarity[i]=((WeightedSum)wsum).getWeight(i)>0;
            }
        }
        else {
            return;
        }
        
        //   Storage for any expressions that need to be extracted from the sum. 
        ArrayList<ASTNode> replVars=new ArrayList<ASTNode>();
        ArrayList<ASTNode> extracted=new ArrayList<ASTNode>();
        
        for(int i=0; i<optTerms.size(); i++) {
            replVars.add(null);
            extracted.add(null);
        }
        
        collectIdentifiers(m.constraints);
        
        //  Get a list of constraints for each term in the objective function. 
        ArrayList<ArrayList<ASTNode>> optTermCt=new ArrayList<>();
        
        for(int i=0; i<optTerms.size(); i++) {
            if(optTerms.get(i) instanceof Identifier) {
                ArrayList<ASTNode> ctlist=idToCons.get(optTerms.get(i));
                if(ctlist==null) {
                    ctlist=new ArrayList<ASTNode>();
                }
                ArrayList<ASTNode> cts=new ArrayList<ASTNode>();
                for(int j=0; j<ctlist.size(); j++) {
                    if(ctlist.get(j)!=optCt) {
                        cts.add(ctlist.get(j));
                    }
                }
                optTermCt.add(cts);
            }
            else {
                //  If an expression, temporarily replace with a new aux variable.
                ASTNode tmpaux=m.global_symbols.newAuxHelper(optTerms.get(i));
                ASTNode ct=new Equals(optTerms.get(i).copy(), tmpaux);
                
                ASTNode p=optTerms.get(i).getParent();
                p.setChild(optTerms.get(i).getChildNo(), tmpaux);
                
                //  Store
                replVars.set(i, tmpaux);
                extracted.set(i, optTerms.get(i));
                
                // Put the one constraint into optTermCt. 
                ArrayList<ASTNode> cts=new ArrayList<ASTNode>();
                cts.add(ct);
                optTermCt.add(cts);
                
                optTerms.set(i, tmpaux);
            }
        }
        
        //  For each term, if there is only one variable connected to it,
        //  then add the constraints on that variable as well. 
        //  Allows opt. variable to be function of another variable. 
        for(int i=0; i<optTermCt.size(); i++) {
            ASTNode con=new And(optTermCt.get(i));
            
            ArrayList<ASTNode> vars=TabulationUtils.getVariablesOrdered(con);
            
            HashSet<ASTNode> prevVarsSet=new HashSet<>();
            prevVarsSet.add(optTerms.get(i));
            
            for(int j=2; ; j++) {
                if(vars.size()==j) {
                    // Find the one additional variable
                    ASTNode newvar=null;
                    for(int k=0; k<vars.size(); k++) {
                        if(!prevVarsSet.contains(vars.get(k))) {
                            newvar=vars.get(k);
                        }
                    }
                    assert newvar!=null;
                    
                    for(int k=0; k<idToCons.get(newvar).size(); k++) {
                        // Avoid adding back the opt. sum constraint itself. 
                        if(idToCons.get(newvar).get(k)!=optCt) {
                            System.out.println("Adding to constraint set:"+idToCons.get(newvar).get(k));
                            optTermCt.get(i).add(idToCons.get(newvar).get(k));
                        }
                    }
                }
                else {
                    break;
                }
                
                //  Update the previous variables set.
                prevVarsSet.addAll(vars);
                
                //  Update the set of variables. 
                con=new And(optTermCt.get(i));
                vars=TabulationUtils.getVariablesOrdered(con);
            }
        }
        
        System.out.println(optTerms);
        System.out.println(optTermCt);
        
        TabulationUtils tu=new TabulationUtils(m);
        
        ArrayList<ASTNode> newcts=new ArrayList<ASTNode>();
        
        for(int i=0; i<optTerms.size(); i++) {
            //  Make a conjunction of the constraints containing the variable
            //  This will copy the constraints.
            ASTNode con=new And(optTermCt.get(i));
            
            boolean minimising=(optTermsPolarity[i] && min) || (!optTermsPolarity[i] && !min);
            
            ArrayList<ASTNode> vars=TabulationUtils.getVariablesOrdered(con);
            ArrayList<ASTNode> domains=tu.getDomains(vars);
            
            // Remove variables that occur only within the set of constraints. Don't remove the objective variable.
            boolean unroll=false;
            for(int j=0; j<vars.size(); j++) {
                ASTNode var=vars.get(j);
                
                ArrayList<ASTNode> varsdup=TabulationUtils.getVariablesDup(con);
                // Count var. 
                int varcount=0;
                for(int k=0; k<varsdup.size(); k++) {
                    if(varsdup.get(k).equals(var)) {
                        varcount++;
                    }
                }
                
                if(idToCons.containsKey(var) && idToCons.get(var).size()==varcount) {   //  All occurrences of var are in the collection of constraints to tabulate. 
                    //  Shadowing the decision variable -- does this work correctly? Yes it does. 
                    con=new ExistsExpression(vars.get(j), domains.get(j), con);
                    unroll=true;
                }
            }
            if(unroll) {
                TransformQuantifiedExpression tqe=new TransformQuantifiedExpression(m);
                con=tqe.transform(con);
            }
            
            System.out.println("About to tabulate (objective):"+con);
            
            ASTNode newtable=tu.makeTableLongDominance(con, nodelimit, optTerms.get(i), minimising);
            
            if(newtable==null) {
                //  Put things back.
                if(extracted.get(i)!=null) {
                    System.out.println("Failed to tabulate. Restoring term of objective function.");
                    
                    //  Replace the temporary aux variable in wsum with extracted.get(i)
                    wsum.setChild(i, extracted.get(i));
                    
                    //  Delete the aux variable
                    m.global_symbols.deleteSymbol(replVars.get(i).toString());
                }
            }
            else {
                ArrayList<ASTNode> toreplace=optTermCt.get(i);
                //  Replace the original constraints with 'true'
                for(int j=0; j<toreplace.size(); j++) {
                    if(toreplace.get(j).getParent()!=null) {
                        toreplace.get(j).getParent().setChild(toreplace.get(j).getChildNo(), new BooleanConstant(true));
                    }
                }
                newcts.add(newtable);
            }
        }
        
        //  Add the new table constraints. 
        m.constraints.setChild(0, new And(m.constraints.getChild(0), new And(newcts)));
    }
    
    void findOptCt(ASTNode a) {
        if(a.equals(optVar)) {
            ASTNode p=a.getParent();
            while(! p.isRelation()) {
                p=p.getParent();
            }
            optCt=p;
            return;
        }
        
        for(int i=0; i<a.numChildren() && optCt==null; i++) {
            findOptCt(a.getChild(i));
        }
    }
    
    // Count occurrences of each variable, and collect all constraints mentioning each
    // variable that occurs in the optimisation function (sum). 
    void collectIdentifiers(ASTNode curnode) {
        if(curnode instanceof Identifier) {
            //  Find the constraint containing curnode.
            ASTNode p=curnode.getParent();
            while(! (p.isRelation() && p.getDimension()==0)) {
                p=p.getParent();
            }
            if(! idToCons.containsKey(curnode)) {
                idToCons.put(curnode, new ArrayList<ASTNode>());
            }
            idToCons.get(curnode).add(p);
	    }
	    else {
	        for(int i=0; i<curnode.numChildren(); i++) {
	            collectIdentifiers(curnode.getChild(i));
	        }
	    }
	}
    
    /////////////////////////////////////////////////////////////////////////
    // Evaluate the three single-constraint heuristics
    
    private String heuristic(ASTNode curnode) {
        ArrayList<ASTNode> varlist=TabulationUtils.getVariablesOrdered(curnode);
        ArrayList<ASTNode> varlistdups=TabulationUtils.getVariablesDup(curnode);
        
        //  Duplicate variables and within a reasonable size bound.
        //  Should perhaps look at domain size rather than # variables.
        if(varlist.size()<varlistdups.size() && varlist.size()<=10) {
            if(verbose) {
                System.out.println("H1");
            }
            return "DuplicateVariables";
        }
        
        //  Tree size is much larger than the number of variables.
        //  Either the expression is highly complex or it contains a large 
        //  number of constants. 
        if(curnode.treesize() > 5*varlist.size()) {
            if(verbose) {
                System.out.println("H2");
            }
            return "LargeAST";
        }
        
        // Constraint does not get GAC, and it overlaps with some other
        // constraint that does get GAC or similar. Uses the strongProp method. 
        if(!curnode.strongProp() && varlist.size()<=10) {
            ASTNode constraints=m.constraints.getChild(0);
            if(constraints instanceof And) {
                for(int i=0; i<constraints.numChildren(); i++) {
                    ASTNode c=constraints.getChild(i);
                    if(c.strongProp()) {
                        for(int varidx=0; varidx<varlist.size(); varidx++) {
                            if(c.contains(varlist.get(varidx))) {
                                if(verbose) {
                                    System.out.println("H3");
                                }
                                return "WeakPropagation";
                            }
                        }
                    }
                }
            }
        }
        
        return null;
    }
    
    //  Does outer contain inner (not a copy of inner)?
    public boolean contains(ASTNode outer, ASTNode inner) {
        if (outer==inner) {
            return true;
        }
        else {
            for (int i=0; i < outer.numChildren(); i++) {
                if (contains(outer.getChild(i), inner)) {
                    return true;
                }
            }
        }
        return false;
    }
    
    /////////////////////////////////////////////////////////////////////////
    //  Actually perform the tabulation of an expression.
    
    public ASTNode tabulate(ASTNode totab, long nodelimit, boolean shorttable, String heuristic) {
        ASTNode a=tu.normalise(totab);
        
        if(CmdFlags.tabulate_diagnostics) {
            CmdFlags.println(ANSI_RED+heuristic+ANSI_RESET+"   Attempting tabulation: "+a);
        }
        
        //  Check the cache.
        TabulationUtils.RetPair ret = tu.tryCacheNormalised(totab, shorttable);
        if(ret.nodereplace != null) {
            if(CmdFlags.tabulate_diagnostics) {
                CmdFlags.println(ANSI_GREEN+"Tabulated"+ANSI_RESET+" by retrieving from cache.");
            }
            return ret.nodereplace.current_node;
        }
        
        //  First normalise  before generating table.
        //ASTNode a=tu.normalise(totab);
        ASTNode newTable;
        long nodecount=-1;
        
        if(!shorttable) {
            newTable = tu.makeTableLong(a, nodelimit);
            nodecount=tu.nodecount;
        }
        else {
            //  Make short table constraint
            if(nodelimit==Long.MAX_VALUE) {
                //  No limit.
                newTable = tu.makeTableShort(a, nodelimit, nodelimit, nodelimit);
            }
            else {
                newTable = tu.makeTableShort(a, 10000, 100000, 100000);
            }
        }
        
        if(newTable==null) {
            tu.saveToFailCache(ret.expstring);
            if(verbose) {
                System.out.println("Adding to failCache:"+ret.expstring);
            }
        }
        else {
            // Save in the cache
            tu.saveToCacheNormalised(ret.expstring, a, newTable);
            
            if(CmdFlags.tabulate_diagnostics) {
                CmdFlags.println(ANSI_GREEN+"Tabulated"+ANSI_RESET+" in nodes:"+nodecount);
            }
        }
        return newTable;
    }
    
}


