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

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.io.Writer;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Objects;

import savilerow.*;
import savilerow.expression.*;
import savilerow.treetransformer.*;

// Very straightforward implementation of a symbol table that maps
// variables (looked up by name) to their domain and category (parameter or decision)
// Quantifier variables are not included here, only global ones.

public class SymbolTable implements Serializable {
    private static final long serialVersionUID = 1L;
    
    public transient Model m;
    
    public ArrayDeque<ASTNode> lettings_givens;    // Lettings, givens, wheres, finds in order.
    
    // Category has an entry for each symbol.
    public HashMap<String, categoryentry> category;
    
    public categoryentry category_first;
    public categoryentry category_last;
    
    // Arraylist version of the above for serialization.
    private ArrayList<categoryentry> category_list;
    
    // domains and constant_matrices have entries whenever the symbol has an
    // associated domain and/or constant matrix
    
    // Domain could be an identifier -- should be defined in a  letting.
    private HashMap<String, ASTNode> domains;
    
    public transient HashMap<String, String> represents_ct;    // String representation of the ct the aux var represents.
    
    // Yet another data structure -- for matrices that have been replaced with
    // atomic variables. 
    public HashMap<String, ASTNode> deleted_matrices;
    
    public HashMap<String, replaces_matrix_entry> replaces_matrix;    // as in replaces["M___5___4"]=<"M", [5,4]>
    
    int auxvarcounter;
    
    public HashMap<ASTNode, ASTNode> replacements;    // Variables that have been deleted and replaced with either
    // another variable, a constant or a simple expression like a negation of a variable.
    public HashMap<ASTNode, ASTNode> replacements_domains;    // Domains for deleted vars at the point of deletion.
    public HashMap<ASTNode, Integer> replacements_category;    // Category of deleted vars at point of deletion.
    
    //  Special hash-tables for marking variables as bool, int or both. 
    HashSet<String> boolvar_bool;    // Not included in .equals comparison or copy.
    HashSet<String> boolvar_int;
    
    //   When encoding to SAT, some variables marked as needing direct or order encoding (or both).
    HashSet<String> directvar_sat;
    HashSet<String> ordervar_sat;

    //   When encoding to SMT, some variables marked as integers.
    HashSet<String> var_integer;

    //   When encoding to SMT, some variables marked as bit vectors.
    HashSet<String> var_bitVector;

    //   When encoding to SMT, some variables marked as booleans
    HashSet<String> var_boolean;

    public SymbolTable() {
        lettings_givens = new ArrayDeque<ASTNode>();
        domains = new HashMap<String, ASTNode>();

        // This is the ordering on the symbols for output.
        category = new HashMap<String, categoryentry>();
        category_first = null;
        category_last = null;

        represents_ct = new HashMap<String, String>();
        auxvarcounter = 0;

        // Extra data for gecode and minizinc output.
        boolvar_bool = new HashSet<String>();
        boolvar_int = new HashSet<String>();

        deleted_matrices = new HashMap<String, ASTNode>();
        replaces_matrix = new HashMap<String, replaces_matrix_entry>();

        replacements = new HashMap<ASTNode, ASTNode>();
        replacements_domains = new HashMap<ASTNode, ASTNode>();
        replacements_category = new HashMap<ASTNode, Integer>();
    }
    
    private void category_put_end(String name, int cat) {
        if (category_last == null) {
            assert category_first == null;
            category_first = category_last = new categoryentry(name, cat, null, null);
        } else {
            categoryentry tmp = new categoryentry(name, cat, category_last, null);
            category_last.next = tmp;
            category_last = tmp;
        }
        category.put(name, category_last);
    }
    
    @Override
    public boolean equals(Object b) {
        if (! (b instanceof SymbolTable)) {
            return false;
        }
        SymbolTable c = (SymbolTable) b;
        
        // Omitting m.
        
        // Irritatingly ArrayDeque does not have its own .equals.
        if(! Arrays.equals(lettings_givens.toArray(), c.lettings_givens.toArray())) {
            return false;
        }
        
        if (! c.category.equals(category)) {
            return false;
        }
        // Iterate down the categoryentry list checking equality. Can't do this recursively because it blows the stack.
        categoryentry iter_this = category_first;
        categoryentry iter_other = c.category_first;
        while (iter_this != null || iter_other != null) {
            if (iter_this == null || iter_other == null) {
                // One is null and the other is not.
                return false;
            }

            if (! iter_this.equals(iter_other)) {
                return false;
            }

            assert iter_this.next == null || iter_this.next.prev == iter_this;
            assert iter_other.next == null || iter_other.next.prev == iter_other;
            assert iter_this.next != null || iter_this == category_last;
            assert iter_other.next != null || iter_other == c.category_last;

            iter_this = iter_this.next;
            iter_other = iter_other.next;
        }

        if (! c.domains.equals(domains)) {
            return false;
        }
        
        if (! c.represents_ct.equals(represents_ct)) {
            return false;
        }
        
        if (! c.deleted_matrices.equals(deleted_matrices)) {
            return false;
        }
        if (! c.replaces_matrix.equals(replaces_matrix)) {
            return false;
        }
        if (c.auxvarcounter != auxvarcounter) {
            return false;
        }

        if (! c.replacements.equals(replacements)) {
            return false;
        }
        if (! c.replacements_domains.equals(replacements_domains)) {
            return false;
        }
        if (! c.replacements_category.equals(replacements_category)) {
            return false;
        }

        return true;
    }
    
    @Override public int hashCode() {
        // The linked list  -- generate a hash that depends on the order of variable names. 
        int hashlist=0;
        categoryentry iter = category_first;
        while (iter != null) {
            hashlist=(6091*hashlist) + (iter.name.hashCode());
            iter=iter.next;
        }
        
        return Objects.hash(Arrays.hashCode(lettings_givens.toArray()), category, 
            hashlist, domains, represents_ct, deleted_matrices, replaces_matrix, 
            auxvarcounter, replacements, replacements_domains, replacements_category);
    }
    
    public SymbolTable copy(Model new_m) {
        SymbolTable st = new SymbolTable();
        st.m=new_m;
        TransformFixSTRef tf = new TransformFixSTRef(new_m);
        
        // Copy lettings, givens etc in sequence.
        for (Iterator<ASTNode> itr = lettings_givens.iterator(); itr.hasNext();) {
            ASTNode letgiv = itr.next();
            st.lettings_givens.addLast(tf.transform(letgiv.copy()));
        }
        
        categoryentry cur = category_first;
        while (cur != null) {
            st.category_put_end(cur.name, cur.cat);
            cur = cur.next;
        }
        
        for (String domst : domains.keySet()) {
            st.domains.put(domst, tf.transform(domains.get(domst).copy()));
        }
        
        st.represents_ct = new HashMap<String, String>(represents_ct);
        for (String delst : deleted_matrices.keySet()) {
            st.deleted_matrices.put(delst, tf.transform(deleted_matrices.get(delst).copy()));
        }
        for (String repmat : replaces_matrix.keySet()) {
            replaces_matrix_entry r1 = new replaces_matrix_entry(replaces_matrix.get(repmat).name, new ArrayList<Long>(replaces_matrix.get(repmat).idx));
            st.replaces_matrix.put(repmat, r1);
        }
        st.auxvarcounter = auxvarcounter;
        
        for (ASTNode rep1 : replacements.keySet()) {
            st.replacements.put(tf.transform(rep1.copy()), tf.transform(replacements.get(rep1).copy()));
        }
        for (ASTNode rep2 : replacements_domains.keySet()) {
            st.replacements_domains.put(tf.transform(rep2.copy()), tf.transform(replacements_domains.get(rep2).copy()));
        }
        for (ASTNode rep3 : replacements_category.keySet()) {
            st.replacements_category.put(tf.transform(rep3.copy()), (int) replacements_category.get(rep3));
        }
        
        return st;
    }
    
    // To add parameters
    public void newVariable(String name, ASTNode dom, int cat) {
        assert ! category.containsKey(name);
        domains.put(name, dom);
        category_put_end(name, cat);
    }
    
    // To add variables replacing a matrix
    public void newVariable(String name, ASTNode dom, int cat, ASTNode replaces, ArrayList<Long> indices) {
        assert ! category.containsKey(name);
        domains.put(name, dom);
        if (dom.getCategory() == ASTNode.Constant) {
            ArrayList<Intpair> set = dom.getIntervalSet();
            if (set.size() == 0) {
                CmdFlags.println("ERROR: Empty domain");
            }
        }
        categoryentry c = category.get(replaces.toString());        // Add directly before this

        categoryentry newcat = new categoryentry(name, cat, c.prev, c);

        // stitch it in
        if (newcat.next == null) {
            category_last = newcat;
        } else {
            newcat.next.prev = newcat;
        }
        if (newcat.prev == null) {
            category_first = newcat;
        } else {
            newcat.prev.next = newcat;
        }

        category.put(name, newcat);

        replaces_matrix.put(name, new replaces_matrix_entry(replaces.toString(), new ArrayList<Long>(indices)));
    }

    //////////////////////////////////////////////////////////////////////////// 
    // Unify two equal decision variables.
    // Returns true iff one variable was deleted. 
    
    public void unifyVariables(ASTNode id1, ASTNode id2) {
        assert id1.getCategory() == ASTNode.Decision && id2.getCategory() == ASTNode.Decision;
        
        // If one is an aux var and the other isn't, the aux var will be deleted.
        // If one has the prefix "incumbent_" generated by Conjure for SNS incumbent variables,
        // the incumbent variable will be deleted.
        // If id2 is to be preserved and id1 not, then swap. 
        if(category.get(id1.toString()).cat == ASTNode.Auxiliary 
            || (id1.toString().length()>=10 && id1.toString().substring(0,10).equals("incumbent_"))
            || (!preserveVariable(id1) && preserveVariable(id2)) ) {
            // Swap.
            ASTNode temp = id1;
            id1 = id2;
            id2 = temp;
        }
        // There is always a branchingon list, so it doesn't matter which one is eliminated.
        
        ArrayList<Intpair> id1dom=getDomain(id1.toString()).getIntervalSet();
        ArrayList<Intpair> id2dom=getDomain(id2.toString()).getIntervalSet();
        ArrayList<Intpair> intersect=Intpair.intersection(id1dom, id2dom);
        //  Takes the 'booleanness' from id1.
        ASTNode intersectDomain=Intpair.makeDomain(intersect, getDomain(id1.toString()).isBooleanSet());
        
        // Check if either variable is to be preserved.
        
        assert !preserveVariable(id2);  //  If this were the case, they should have been swapped. 
        setDomain(id1.toString(), intersectDomain);
        
        // id2 will be replaced by id1.
        replacements.put(id2, id1);
        // this hash table will be used to find its value.
        replacements_domains.put(id2, getDomain(id2.toString()));
        replacements_category.put(id2, category.get(id2.toString()).cat);
        
        // Delete id2 in Symboltable.
        deleteSymbol(id2.toString());
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Unify two decision variables when one is the negation of the other.
    
    public void unifyVariablesNegated(ASTNode id1, ASTNode id2) {
        assert id1.getCategory() == ASTNode.Decision && id2.getCategory() == ASTNode.Decision;
        assert id2 instanceof Negate;
        id2=id2.getChild(0);  // Strip off the negation.
        
        assert id1.isRelation() && id2.isRelation();
        
        // If one is an aux var and the other isn't, the aux var should be deleted.
        if (category.get(id1.toString()).cat == ASTNode.Auxiliary
            || (!preserveVariable(id1) && preserveVariable(id2)) ) {
            // Swap.
            ASTNode temp = id1;
            id1 = id2;
            id2 = temp;
        }
        
        assert !preserveVariable(id2);
        // id2 will be replaced by not id1.
        replacements.put(id2, new Negate(id1));
        // this hash table will be used to find its value.
        replacements_domains.put(id2, getDomain(id2.toString()));
        replacements_category.put(id2, category.get(id2.toString()).cat);
        
        // get rid of id2 in Symboltable. Don't need to worry about
        // branchingon or other places because it will be done using ReplaceASTNode.
        deleteSymbol(id2.toString());
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Unify two decision variables when one is a linear transformation of the other.
    
    //  This method apparently does not work and the reasons are not clear to me. 
    public void unifyVariablesLinear(ASTNode id1, ASTNode ex2) {
        System.out.println("unifyVariablesLinear "+id1+" "+ex2);
        System.out.println(id1.getIntervalSetExp());
        System.out.println(ex2.getIntervalSetExp());
        System.out.println(getDomain(id1.toString()));
        assert id1.getCategory() == ASTNode.Decision && ex2.getCategory() == ASTNode.Decision;
        assert id1 instanceof Identifier;
        assert !preserveVariable(id1);
        // id1 is replaced with ex2 everywhere, and id1 is removed.
        
        replacements.put(id1, ex2);
        // this hash table will be used to find its value.
        replacements_domains.put(id1, getDomain(id1.toString()));
        replacements_category.put(id1, category.get(id1.toString()).cat);
        
        // get rid of id1 in Symboltable. Don't need to worry about
        // branchingon or other places because it will be done using ReplaceASTNode.
        deleteSymbol(id1.toString());
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // 
    // Delete variable when it is assigned.
    
    public void assignVariable(ASTNode id, ASTNode value) {
        assert (!CmdFlags.getUseAggregate()) || CmdFlags.getAfterAggregate();
        assert id instanceof Identifier;
        assert value.isConstant();
        assert getDomain(id.toString()).containsValue(value.getValue());
        assert id.getModel().global_symbols==this;
        assert !preserveVariable(id);
        
        if(id.isRelation() && !value.isRelation()) {
            long v=value.getValue();
            assert v>=0 && v<=1;
            value=new BooleanConstant(v==1);
        }
        
        //System.out.println("Assign "+id+", "+value+" with domains "+getDomain(id.toString()));
        replacements.put(id, value);        // This will be used to retrieve the value when parsing solver output.
        replacements_domains.put(id, getDomain(id.toString()));
        replacements_category.put(id, category.get(id.toString()).cat);
        
        deleteSymbol(id.toString());
        
        if(m.sns != null && CmdFlags.getMinionSNStrans()) {
            ASTNode primaries=m.sns.getChild(0).getChild(0);
            ASTNode incumbents=m.sns.getChild(0).getChild(1);
            
            ///  Horrifying cost of n just to assign a variable when using SNS.
            for(int i=1; i<primaries.numChildren(); i++) {
                if(primaries.getChild(i).equals(id)) {
                    ASTNode incumbent=incumbents.getChild(i);
                    
                    if(getDomain(incumbent.toString())!=null && !preserveVariable(incumbent)) {
                        //  If incumbent has not already been deleted, by having a single value in domain...
                        assignVariable(incumbent, value.copy());
                    }
                    break;
                }
            }
        }
    }
    
    private HashSet<ASTNode> presVarsSet;
    
    public boolean preserveVariable(ASTNode id) {
        if(m.preserveVariables==null) {
            return false;
        }
        if(presVarsSet==null) {
            if(! (m.preserveVariables instanceof CompoundMatrix)) {
                //  preserveVariables list is not fully evaluated yet -- preserve all variables. 
                return true;
            }
            presVarsSet=new HashSet<ASTNode>(m.preserveVariables.getChildren(1));  //  Dump the contents of preserveVariables matrix into the HashSet
        }
        
        return presVarsSet.contains(id);
    }
    
    public ASTNode getDomain(String varid) {
        return domains.get(varid);
    }
    
    public void setDomain(String varid, ASTNode d) {
        domains.put(varid, d);
    }
    
    public boolean isAuxiliary(String varid) {
        return category.get(varid).cat==ASTNode.Auxiliary;
    }
    
    public HashMap<String, ASTNode> getDomains() { return domains; }
    
    public categoryentry getCategoryFirst() { return category_first; }
    
    public int getCategory(String varid) {
        if (category.get(varid) == null) {
            return ASTNode.Undeclared;
        }
        int i = category.get(varid).cat;
        if (i == ASTNode.Auxiliary) {
            return ASTNode.Decision;
        }
        if (i == ASTNode.ConstantMatrix) {
            return ASTNode.Constant;
        }
        return i;
    }
    
    public boolean hasVariable(String varid) {
        return category.containsKey(varid);
    }
    
    //  Find unused name for new auxiliary id.
    public String newAuxId() {
        String newname = "aux" + auxvarcounter;
        while (category.containsKey(newname)) {
            auxvarcounter++;
            newname = "aux" + auxvarcounter;
        }
        auxvarcounter++;
        return newname;
    }
    
    public Identifier newAuxiliaryVariable(long lb, long ub) {
        String newname = newAuxId();
        if (lb != 0 || ub != 1) {
            domains.put(newname, new IntegerDomain(new Range(NumberConstant.make(lb), NumberConstant.make(ub))));
        } else {
            domains.put(newname, new BooleanDomainFull());
        }
        
        category_put_end(newname, ASTNode.Auxiliary);
        return new Identifier(m, newname);
    }
    
    public Identifier newAuxiliaryVariable(ASTNode dom) {
        String newname = newAuxId();
        
        //  Convert from 0..1 to boolean as in the method above. 
        ArrayList<Intpair> a=dom.getIntervalSet();
        if(a.size()==1 && a.get(0).lower==0 && a.get(0).upper==1) {
            domains.put(newname, new BooleanDomainFull());
        }
        else {
            domains.put(newname, dom.copy());
        }
        
        category_put_end(newname, ASTNode.Auxiliary);
        return new Identifier(m, newname);
    }
    
    // newAuxHelper just takes an expression and makes an auxiliary variable for it.
    // Deals with FilteredDomainStorage. 
    public ASTNode newAuxHelper(ASTNode exp) {
        ArrayList<Intpair> a=exp.getIntervalSetExp();
        ASTNode auxdom=Intpair.makeDomain(a, exp.isRelation());
        auxdom=m.filt.constructDomain(exp, auxdom);  //  Look up stored (filtered) domain if there is one.
        
        ASTNode auxvar=newAuxiliaryVariable(auxdom);
        m.filt.auxVarRepresentsAST(auxvar.toString(), exp);    //  Associate the expression to the variable in FilteredDomainStorage
        return auxvar;
    }
    
    // newAuxHelper just takes an expression and makes an auxiliary variable for it.
    // Deals with FilteredDomainStorage. 
    public ASTNode newAuxHelper(ASTNode exp, ASTNode maxdomain) {
        ArrayList<Intpair> a=exp.getIntervalSetExp();
        ASTNode ints=new Intersect(Intpair.makeDomain(a, exp.isRelation()), maxdomain);
        ASTNode auxdom=m.filt.constructDomain(exp, ints);  //  Look up stored (filtered) domain if there is one.
        auxdom=(new TransformSimplify()).transform(auxdom);
        ASTNode auxvar=newAuxiliaryVariable(auxdom);
        m.filt.auxVarRepresentsAST(auxvar.toString(), exp);    //  Associate the expression to the variable in FilteredDomainStorage
        return auxvar;
    }
    
    //  Used exclusively by class-level flattening.
    public Identifier newAuxiliaryVariable(ASTNode lb, ASTNode ub) {
        String newname = newAuxId();
        domains.put(newname, new IntegerDomain(new Range(lb, ub)));
        category_put_end(newname, ASTNode.Auxiliary);
        return new Identifier(m, newname);
    }
    
    //  Create matrix of aux variables. Also used exclusively by class-level flattening.
    public Identifier newAuxiliaryVariableMatrix(ASTNode lb, ASTNode ub, ArrayList<ASTNode> q_id, ArrayList<ASTNode> qdoms, ArrayList<ASTNode> conditions) {
        // Class-level flattening requires sausage matrix.
        String newname = newAuxId();
        category_put_end(newname, ASTNode.Auxiliary);

        // indexed by the quantifier domains.
        domains.put(newname, new MatrixDomain( new IntegerDomain(new Range(lb, ub)), qdoms, new Container(q_id), new And(conditions)));

        return new Identifier(m, newname);
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // 
    //  Constant matrices
    public void registerConstantMatrix(String name) {
        if (category.containsKey(name)) {            // Should be a parameter...
            assert category.get(name).cat == ASTNode.Parameter;
            // Make it a constant matrix
            category.get(name).cat = ASTNode.ConstantMatrix;
        } else {
            category_put_end(name, ASTNode.ConstantMatrix);
        }
    }
    
    
    
    
    // Add some info that is helpful for debugging
    public void auxVarRepresentsConstraint(String name, String ct) {
        represents_ct.put(name, ct.replaceAll("\n", ""));  // Get rid of any newlines that cause problems in comments.
    }

    public String toString() {
        StringBuilder b = new StringBuilder();
        categoryentry c = category_first;
        while (c != null) {
            String name = c.name;
            ASTNode dom = getDomain(name);
            
            if (getCategory(name) == ASTNode.Parameter) {
                b.append("given ");
            } else if (getCategory(name) == ASTNode.Decision) {
                b.append("find ");
            }
            
            b.append(name);
            b.append(" : ");
            b.append(dom.toString());
            b.append("\n");
            c = c.next;
        }
        return b.toString();
    }

    public boolean simplify() {
        // Simplify the expressions in the domains and matrices of constants.
        TransformSimplify ts = new TransformSimplify();
        
        ArrayList<String> delete_vars = new ArrayList<String>();

        // Simplify lettings_givens.
        int size = lettings_givens.size();
        for (int i =0; i < size; i++) {            // For each one, take it off the front and add back to the end of the deque.
            lettings_givens.addLast(ts.transform(lettings_givens.removeFirst()));
        }
        
        boolean emptyDomain=false;  // set true when we see an empty domain.
        Iterator<Map.Entry<String, ASTNode>> itr = domains.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, ASTNode> d = itr.next();
            
            ASTNode dom = d.getValue();
            // atl.transform(dom);
            dom = ts.transform(dom);
            d.setValue(dom);
            
            // Check for unit domains.  Sometimes arise after unifying two vars,
            // or might be given by the user.
            if (dom.getCategory() == ASTNode.Constant && dom.isFiniteSet()) {
                Intpair bnds = dom.getBounds();
                if(bnds.upper<bnds.lower) {
                    emptyDomain=true;
                }
                if (CmdFlags.getUseDeleteVars() && bnds.lower==bnds.upper) {
                    delete_vars.add(d.getKey());
                }
            }
        }
        
        // Now delete the unit variables.
        if (CmdFlags.getUseDeleteVars() && (!CmdFlags.getUseAggregate() || CmdFlags.getAfterAggregate())) {
            for (int i =0; i < delete_vars.size(); i++) {
                if(getDomain(delete_vars.get(i)) != null) {
                    ASTNode varid=new Identifier(m, delete_vars.get(i));
                    if(!preserveVariable(varid)) {
                        ASTNode value = NumberConstant.make(getDomain(delete_vars.get(i)).getBounds().lower);  // assignVariable converts to bool if necessary
                        assignVariable(varid, value);
                    }
                }
            }
        }
        
        return !emptyDomain;
    }

    public void transform_all(TreeTransformer t) {
        // Poke into every corner and apply t.

        // do lettings_givens
        int size = lettings_givens.size();
        for (int i =0; i < size; i++) {            // For each one, take it off the front and add back to the end of the deque.
            lettings_givens.addLast(t.transform(lettings_givens.removeFirst()));
        }

        // Domains
        Iterator<Map.Entry<String, ASTNode>> itr = domains.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, ASTNode> d = itr.next();
            ASTNode dom = d.getValue();
            d.setValue(t.transform(dom));
        }

        itr = deleted_matrices.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, ASTNode> d = itr.next();
            ASTNode mat = d.getValue();
            d.setValue(t.transform(mat));
        }

        HashMap<ASTNode, ASTNode> newreplacements = new HashMap<ASTNode, ASTNode>();
        Iterator<Map.Entry<ASTNode, ASTNode>> itr2 = replacements.entrySet().iterator();
        while (itr2.hasNext()) {
            Map.Entry<ASTNode, ASTNode> d = itr2.next();
            ASTNode left = t.transform(d.getKey());
            ASTNode right = t.transform(d.getValue());
            newreplacements.put(left, right);
        }
        this.replacements = newreplacements;

        HashMap<ASTNode, ASTNode> newreplacements_domains = new HashMap<ASTNode, ASTNode>();
        itr2 = replacements_domains.entrySet().iterator();
        while (itr2.hasNext()) {
            Map.Entry<ASTNode, ASTNode> d = itr2.next();
            ASTNode left = t.transform(d.getKey());
            ASTNode right = t.transform(d.getValue());
            newreplacements_domains.put(left, right);
        }
        this.replacements_domains = newreplacements_domains;

        HashMap<ASTNode, Integer> newreplacements_category = new HashMap<ASTNode, Integer>();
        Iterator<Map.Entry<ASTNode, Integer>> itr3 = replacements_category.entrySet().iterator();
        while (itr3.hasNext()) {
            Map.Entry<ASTNode, Integer> d = itr3.next();
            ASTNode left = t.transform(d.getKey());
            newreplacements_category.put(left, (int) d.getValue());
        }
        this.replacements_category = newreplacements_category;
    }

    public void substitute(ASTNode toreplace, ASTNode replacement) {
        ReplaceASTNode t = new ReplaceASTNode(toreplace, replacement);

        Iterator<Map.Entry<String, ASTNode>> itr = domains.entrySet().iterator();
        while (itr.hasNext()) {
            Map.Entry<String, ASTNode> d = itr.next();
            ASTNode dom = d.getValue();

            d.setValue(t.transform(dom));
        }

        int size = lettings_givens.size();
        for (int i =0; i < size; i++) {            // For each one, take it off the front and add back to the end of the deque.
            ASTNode letgiv = lettings_givens.removeFirst();
            ASTNode firstchild = letgiv.getChild(0);            // Don't sub into the first child-- it's the identifier.
            letgiv = t.transform(letgiv);
            letgiv.setChild(0, firstchild);
            lettings_givens.addLast(letgiv);
        }
    }

    public boolean typecheck() {
        // At this point, lettings have been substituted in so all things in
        // 'domains' should be of type Domain.
        for (String a : domains.keySet()) {
            ASTNode d = domains.get(a);
            if (! (d instanceof Domain)) {
                CmdFlags.println("ERROR: Found " + d + " when expecting domain for symbol " + a);
                return false;
            }
            if (!d.typecheck(this)) {
                return false;
            }

            if (getCategory(a) == ASTNode.Decision) {
                // Do some extra checks for finiteness for decision variable matrices.
                if (d instanceof MatrixDomain) {
                    for (int i =3; i < d.numChildren(); i++) {
                        if(!(d.getChild(i) instanceof MatrixDomain) && !(d.getChild(i).isFiniteSet())) {
                            CmdFlags.println("ERROR: Found " + d.getChild(i) + " when expecting finite integer domain for indices of matrix variable " + a);
                            return false;
                        }
                    }
                    if (!(d.getChild(0).isFiniteSet())) {
                        CmdFlags.println("ERROR: Found " + d.getChild(0) + " when expecting finite integer domain for decision variable " + a);
                        return false;
                    }
                } else if (!(d.isFiniteSet())) {
                    CmdFlags.println("ERROR: Found " + d + " when expecting finite integer domain for decision variable " + a);
                    return false;
                }
            }
        }
        return true;
    }

    // Delete a symbol from the table for good.
    public void deleteSymbol(String name) {
        assert category.containsKey(name);
        categoryentry c = category.get(name);
        if (c.prev != null) {
            c.prev.next = c.next;
        }
        else {
            category_first = c.next;
        }
        if (c.next != null) {
            c.next.prev = c.prev;
        }
        else {
            category_last = c.prev;
        }
        category.remove(name);
        
        if (domains.containsKey(name)) {
            domains.remove(name);
        }
        if (m.cmstore.hasConstantMatrix(name)) {
            m.cmstore.removeConstantMatrix(name);
        }
    }
    
    public void deleteMatrix(String name) {
        // This symbol is a matrix of decision vars that has been replaced by individual decision vars
        // Delete until parsing.
        assert category.containsKey(name);
        categoryentry c = category.get(name);
        if (c.prev != null) {
            c.prev.next = c.next;
        } else {
            category_first = c.next;
        }
        if (c.next != null) {
            c.next.prev = c.prev;
        } else {
            category_last = c.prev;
        }
        category.remove(name);
        assert domains.containsKey(name);

        deleted_matrices.put(name, domains.get(name));
        domains.remove(name);
    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // 
    // Output methods

    // Mangling and demangling for serialization.

    private void mangle_before_serialization() {
        category_list = new ArrayList<categoryentry>();

        categoryentry cur = category_first;
        while (cur != null) {
            category_list.add(cur);
            cur = cur.next;
        }

        // unlink the list.
        cur = category_first;
        while (cur != null) {
            cur.prev = null;
            cur = cur.next;
            if (cur != null) {
                cur.prev.next = null;
            }
        }
    }

    public void unmangle_after_serialization() {
        if (category_list.size() > 0) {
            category_first = category_list.get(0);
            category_last = category_list.get(category_list.size() - 1);
        } else {
            category_first = null; category_last = null;
        }

        for (int i =0; i < category_list.size(); i++) {
            if (i > 0) {
                category_list.get(i).prev = category_list.get(i - 1);
            } else {
                category_list.get(i).prev = null;
            }

            if (i < category_list.size() - 1) {
                category_list.get(i).next = category_list.get(i + 1);
            } else {
                category_list.get(i).next = null;
            }
        }
        category_list = null;
    }
    
    protected void serialize() {
        mangle_before_serialization();
        try {
            FileOutputStream sts = new FileOutputStream(CmdFlags.auxfile);
            ObjectOutputStream out = new ObjectOutputStream(sts);
            out.writeObject(this);
            out.close();
            sts.close();
        } catch (Exception e) {
            CmdFlags.println(Thread.currentThread().getStackTrace());
            for (StackTraceElement t : e.getStackTrace()) {
                System.out.println(t);
            }
            CmdFlags.println("WARNING: Failed to serialise: " + e);
        }
        unmangle_after_serialization();
    }
    
    public void toMinion(BufferedWriter b) throws IOException {
        assert m.global_symbols == this;
        
        if(CmdFlags.getSaveSymbols()) {
            // Serialise the symbol table only if we are not running the back-end solver.
            serialize();
        }
        
        categoryentry itr = category_first;
        while (itr != null) {
            // Not auxiliary
            if (itr.cat == ASTNode.Decision && !itr.already_written) {
                output_variable(b, itr.name, (Domain) domains.get(itr.name));
                itr.already_written = true;
            }
            itr = itr.next;
        }
        
        // Now do auxiliaries
        itr = category_first;
        while (itr != null) {
            if (itr.cat == ASTNode.Auxiliary && !itr.already_written) {
                output_variable(b, itr.name, (Domain) domains.get(itr.name));
                itr.already_written = true;
            }
            itr = itr.next;
        }
    }

    public void printPrintStmt(BufferedWriter b) throws IOException {
        b.append("PRINT[");
        String sep = "";
        categoryentry itr = category_first;
        while (itr != null) {
            String name = itr.name;
            
            if (itr.cat == ASTNode.Decision) {                // Not auxiliary
                b.append(sep);
                if (getDomain(name) instanceof SimpleDomain) {
                    b.append("[");
                    b.append(name);
                    b.append("]");
                } else {
                    b.append(name);
                }
                sep = ",";
            }
            itr = itr.next;
        }
        // Objective -- last.
        if(m.objective!=null) {
            ASTNode ob=m.objective.getChild(0);
            b.append(sep);
            if(ob instanceof CompoundMatrix) {
                for(int i=1; i<ob.numChildren(); i++) {
                    b.append("[");
                    b.append(ob.getChild(i).toString());
                    b.append("]");
                    if(i<ob.numChildren()-1) {
                        b.append(",");
                    }
                }
            }
            else {
                b.append("[");
                b.append(ob.toString());
                b.append("]");
            }
        }
        
        b.append("]\n");
    }

    public void printAllVariables(Writer b, int cat) throws IOException {
        String sep = "";
        categoryentry itr = category_first;
        while (itr != null) {
            String name = itr.name;            // (String) d.getKey();

            if (itr.cat == cat) {
                b.append(sep);
                b.append(name);
                sep = ",";
            }
            itr = itr.next;
        }

    }
    
    public void printAllVariables(Writer b) throws IOException {
        String sep = "";
        categoryentry itr = category_first;
        while (itr != null) {
            String name = itr.name;
            
            if (itr.cat == ASTNode.Decision || itr.cat == ASTNode.Auxiliary) {
                b.append(sep);
                b.append(name);
                sep = ",";
            }
            itr = itr.next;
        }
    }
    
    //  Only prints one of a boolean/integer pair.
    public boolean printAllVariablesFlatzinc(StringBuilder b, int cat) {
        String sep = "";
        categoryentry itr = category_first;
        boolean hasVariables=false;
        while (itr != null) {
            String name = itr.name;
            
            if (itr.cat == cat) {
                b.append(sep);
                ASTNode dom=getDomain(name);
                if (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) {
                    if (boolvar_int.contains(name)) {
                        b.append(name + "_INTEGER");
                    } else if (boolvar_bool.contains(name)) {
                        b.append(name + "_BOOL");
                    } else {
                        assert false : "Something strange has happened: var with name " + name + " is apparently not used anywhere.";
                    }
                } else {
                    b.append(name);
                }
                hasVariables=true;
                sep = ",";
            }
            itr = itr.next;
        }
        return hasVariables;
    }
    
    public boolean printAllVariablesFlatzincExcept(StringBuilder b, int cat, String except) {
        String sep = "";
        categoryentry itr = category_first;
        boolean hasVariables=false;
        while (itr != null) {
            String name = itr.name;
            
            if (itr.cat == cat && ! name.equals(except)) {
                b.append(sep);
                ASTNode dom=getDomain(name);
                if (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) {
                    if (boolvar_int.contains(name)) {
                        b.append(name + "_INTEGER");
                    } else if (boolvar_bool.contains(name)) {
                        b.append(name + "_BOOL");
                    } else {
                        assert false : "Something strange has happened: var with name " + name + " is apparently not used anywhere.";
                    }
                } else {
                    b.append(name);
                }
                hasVariables=true;
                sep = ",";
            }
            itr = itr.next;
        }
        return hasVariables;
    }
    
    // Output variable declarations.
    private void output_variable(BufferedWriter b, String name, Domain dom) throws IOException {
        String ct = represents_ct.get(name);
        if (ct == null) {
            ct = "";
        }
        if(dom.isBooleanSet()) {
            b.append("BOOL " + name + " #" + ct + "\n");
            if((!dom.containsValue(0)) && (!dom.containsValue(1))) {
                b.append("**CONSTRAINTS**\n");
                b.append("false()  # Empty Boolean domain, faked with false() constraint.\n");
                b.append("**VARIABLES**\n");
            }
            else if((!dom.containsValue(0)) || (!dom.containsValue(1))) {
                b.append("**CONSTRAINTS**\n");
                Intpair bnds = dom.getBounds();
                b.append("w-inintervalset(" + name + ", [");
                b.append(String.valueOf(bnds.lower));
                b.append(",");
                b.append(String.valueOf(bnds.upper));
                b.append("])\n");
                b.append("**VARIABLES**\n");
            }
        }
        else if (dom instanceof SimpleDomain) {
            ArrayList<Intpair> setintervals = dom.getIntervalSet();
            if (setintervals.size() > 0) {
                long rangesize = setintervals.get(setintervals.size() - 1).upper - setintervals.get(0).lower + 1L;

                if (CmdFlags.getUseBoundVars() && rangesize > Constants.boundvar_threshold) {
                    b.append("BOUND " + name + " #" + ct + "\n");
                } else {
                    b.append("DISCRETE " + name + " #" + ct + "\n");
                }

                b.append("{" + setintervals.get(0).lower + ".." + setintervals.get(setintervals.size() - 1).upper + "}\n");
                if (setintervals.size() > 1) {                    // It's not a complete range; need to knock out some vals.
                    b.append("**CONSTRAINTS**\n");
                    b.append("w-inintervalset(" + name + ", [");
                    for (int i =0; i < setintervals.size(); i++) {
                        b.append(String.valueOf(setintervals.get(i).lower));
                        b.append(",");
                        b.append(String.valueOf(setintervals.get(i).upper));
                        if (i < setintervals.size() - 1) {
                            b.append(",");
                        }
                    }
                    b.append("])\n");
                    b.append("**VARIABLES**\n");
                }
            } else {
                // Empty domain
                b.append("DISCRETE " + name + " #" + ct + "\n");
                b.append("{0..0}  #  This is an empty domain. Faking that by using 0..0 and the false() constraint below.\n");
                b.append("**CONSTRAINTS**\n");
                b.append("false()\n");
                b.append("**VARIABLES**\n");
            }
        } else {
            assert false;
        }

    }

    //////////////////////////////////////////////////////////////////////////// 
    // 
    // Flatzinc output
    
    // Methods for marking BooleanDomain variables as bool or int or both.
    
    public void markAsBoolFlatzinc(String name) {
        boolvar_bool.add(name);
    }

    public void markAsIntFlatzinc(String name) {
        boolvar_int.add(name);
    }
    
    public void toFlatzinc(BufferedWriter b) throws IOException {
        categoryentry itr = category_first;
        StringBuffer c=new StringBuffer();
        while (itr != null) {
            if(itr.cat == ASTNode.Decision || itr.cat == ASTNode.Auxiliary) {
                Domain dom = (Domain) getDomain(itr.name);
                output_variable_flatzinc(b, itr.name, dom, c, itr.cat==ASTNode.Auxiliary);
            }
            itr = itr.next;
        }
        b.append(c);
        
        // bool2int constraints
        itr = category_first;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            if((itr.cat == ASTNode.Decision || itr.cat == ASTNode.Auxiliary) && (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) 
                && boolvar_bool.contains(name) && boolvar_int.contains(name)) {
                b.append("constraint bool2int(" + name + "_BOOL," + name + "_INTEGER);\n");
            }
            itr = itr.next;
        }
    }
    
    // Output variable declarations.
    private void output_variable_flatzinc(BufferedWriter b, String name, Domain dom, StringBuffer c, boolean isAux) throws IOException {
        // b is for variables, c is for constraints.
        String ct = represents_ct.get(name);
        if (ct == null) {
            ct = "";
        }
        if (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) {
            boolean boolInFznSearch = m.boolForFznSearch(new Identifier(m, name));
            
            boolean outputBool=boolvar_bool.contains(name) || boolInFznSearch;
            boolean outputInt=boolvar_int.contains(name) || !boolInFznSearch;
            
            if(outputBool) {
                b.append("var bool: " + name + "_BOOL");
                // i.e. not auxiliary and not also present as an int.
                if(!isAux && !boolvar_int.contains(name)) {
                    b.append(":: output_var ");
                }
                if(isAux) {
                    b.append(":: var_is_introduced ");
                }
                b.append(";\n");
            }
            if(outputInt) {
                b.append("var {0,1}: " + name + "_INTEGER ");
                if(!isAux) {
                    b.append(":: output_var ");
                }
                if(isAux) {
                    b.append(":: var_is_introduced ");
                }
                b.append(";\n");
            }
            
            ArrayList<Intpair> set=dom.getIntervalSet();
            assert set.size()<=1;
            if(set.size()==0 || set.get(0).lower != 0 || set.get(0).upper != 1) {
                //  Not just a 0..1 interval. 
                if(set.size()==0) {
                    c.append("constraint int_eq(0,1); % Variable "+name+" has empty domain.\n");
                }
                else {
                    if(outputBool) {
                        c.append("constraint bool_eq("+name+"_BOOL,"+(set.get(0).lower==0?false:true)+"); % Variable "+name+" has singleton domain.\n");
                    }
                    if(outputInt) {
                        c.append("constraint int_eq("+name+"_INTEGER,"+set.get(0).lower+"); % Variable "+name+" has singleton domain.\n");
                    }
                }
            }
        }
        else if (dom instanceof SimpleDomain) {
            
            /*ArrayList<Intpair> set = dom.getIntervalSet();
            if(set.size()==0) {
                b.append("var 0..0 : " + name);
                if (category.get(name).cat == ASTNode.Decision) {
                    b.append("::output_var");
                }
                //b.append("; % Empty domain simulated with 0..0 and bool_eq(true,false). " + ct + "\n");
                b.append(";\n");
                c.append("constraint bool_eq(true,false);\n");  // Empty domain. 
            }
            else {
                b.append("var " + set.get(0).lower + ".." + set.get(set.size()-1).upper + ": " + name);
                // i.e. not auxiliary
                if (category.get(name).cat == ASTNode.Decision) {
                    b.append("::output_var");
                }
                //b.append("; %" + ct + "\n");
                b.append(";\n");
    
                if (set.size() > 1) {                // It's not a complete range
                    c.append("constraint set_in(" + name + ",{");
                    for (int i =0; i < set.size(); i++) {
                        for (long j = set.get(i).lower; j <= set.get(i).upper; j++) {
                            c.append(j);
                            if (i < set.size() - 1 || j < set.get(i).upper) {
                                c.append(",");
                            }
                        }
                    }

                    c.append("});\n");
                }
            }*/
            
            ArrayList<Intpair> set = dom.getIntervalSet();
            if(set.size()==0) {
                b.append("var 0..1 : " + name);
                if(!isAux) {
                    b.append(":: output_var ");
                }
                if(isAux) {
                    b.append(":: var_is_introduced ");
                }
                b.append(";\n");
                c.append("constraint int_eq(0,1); % Variable "+name+" has empty domain.\n");
            }
            else {
                b.append("var ");
                if(set.size()==1) {
                    b.append(set.get(0).lower + ".." + set.get(0).upper);  // One interval
                }
                else {
                    //  Multiple intervals -- write out a set of values. 
                    b.append("{");
                    for (int i =0; i < set.size(); i++) {
                        for (long j = set.get(i).lower; j <= set.get(i).upper; j++) {
                            b.append(String.valueOf(j));
                            if (i < set.size() - 1 || j < set.get(i).upper) {
                                b.append(",");
                            }
                        }
                    }
                    b.append("}");
                }
                b.append(": ");
                b.append(name);
                
                if(!isAux) {
                    b.append(":: output_var ");
                }
                if(isAux) {
                    b.append(":: var_is_introduced ");
                }
                b.append(";\n");
            }
        } else {
            assert false;
        }

    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // Minizinc
    
    public void toMinizinc(StringBuilder b) {
        if(CmdFlags.getSaveSymbols()) {
            // Serialise the symbol table only if given the save symbols flag.
            serialize();
        }
        
        categoryentry itr = category_first;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            // Not auxiliary
            if (itr.cat == ASTNode.Decision) {
                output_variable_minizinc(b, name, dom, false);
            }
            itr = itr.next;
        }

        // Now do auxiliaries
        itr = category_first;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            // Not auxiliary
            if (itr.cat == ASTNode.Auxiliary) {
                output_variable_minizinc(b, name, dom, true);
            }
            itr = itr.next;
        }
        
        // Link boolean and integer variables.
        itr = category_first;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            if ((itr.cat == ASTNode.Decision || itr.cat == ASTNode.Auxiliary) && (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) 
                && boolvar_bool.contains(name) && boolvar_int.contains(name)) {
                b.append("constraint bool2int(" + name + "_BOOL) = " + name + "_INTEGER;\n");
            }
            itr = itr.next;
        }
    }
    
    // Output variable declarations -- minizinc
    private void output_variable_minizinc(StringBuilder b, String name, Domain dom, boolean isAux) {
        String ct = represents_ct.get(name);
        if (ct == null) {
            ct = "";
        }
        String annot=isAux?" :: var_is_introduced :: is_defined_var ":"";
        
        if(dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) {
            if (boolvar_bool.contains(name)) {
                b.append("var bool: " + name + "_BOOL"+annot+"; %" + ct + "\n");
            }
            if (boolvar_int.contains(name)) {
                b.append("var {0,1}: " + name + "_INTEGER"+annot+"; %" + ct + "\n");
            }
        }
        else if(dom instanceof SimpleDomain) {
            ArrayList<Intpair> set = dom.getIntervalSet();
            if (set.size() == 0) {
                // empty domain
                b.append("var 1..0: " + name);
            } else if (set.size() > 1) { // It's not a complete range:
                // Output something like this:
                // set of int: aux1765 = 2..5 union 10..20;
                // var aux1765 : x;
                String setname = newAuxId();
                b.append("set of int : " + setname + " = ");
                for (int i =0; i < set.size(); i++) {
                    b.append(set.get(i).lower + ".." + set.get(i).upper);
                    if (i < set.size() - 1) {
                        b.append(" union ");
                    }
                }
                b.append(";\n");
                b.append("var " + setname + " : " + name);

            } else {
                b.append("var " + set.get(0).lower + ".." + set.get(0).upper + ": " + name);
            }
            b.append(annot);
            b.append("; %" + ct + "\n");
        }
        else {
            assert false;
        }
    }
    
    public void showVariablesMinizinc(StringBuilder b) {
        categoryentry itr = category_first;
        boolean trailingcomma = false;
        while (itr != null) {
            String name = itr.name;
            Domain dom = (Domain) getDomain(name);

            // Not auxiliary
            if (itr.cat == ASTNode.Decision) {
                b.append("show(");

                if (dom.isBooleanSet() || (dom.isIntegerSet() && dom.getBounds().equals(new Intpair(0,1)))) {
                    if (boolvar_bool.contains(name)) {
                        b.append(name + "_BOOL");
                    } else if (boolvar_int.contains(name)) {
                        b.append(name + "_INTEGER");
                    }
                } else {
                    b.append(name);
                }

                b.append("),\" \",");
                trailingcomma = true;
            }
            itr = itr.next;
        }

        // take off trailing comma.
        if (trailingcomma) {
            b.deleteCharAt(b.length() - 1);
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // Data and functions for SAT output.
    
    public void markAsDirectSAT(String name) {
        if(directvar_sat==null) directvar_sat=new HashSet<String>();
        directvar_sat.add(name);
    }
    
    public void markAsOrderSAT(String name) {
        if(ordervar_sat==null) ordervar_sat=new HashSet<String>();
        ordervar_sat.add(name);
    }

    public boolean isDirectSAT(String name) {
        if(directvar_sat==null) {
            return false;
        }
        else {
            return directvar_sat.contains(name);
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // Data and functions for SMT output.

    public void markAsInteger(String name) {
        if(var_integer ==null) var_integer =new HashSet<String>();
        var_integer.add(name);
    }

    public boolean isInteger(String name) {
        if(var_integer ==null) {
            return false;
        }
        else {
            return var_integer.contains(name);
        }
    }

    public boolean isBitVector(String name) {
        if (var_bitVector == null) {
            return false;
        }
        else {
            return var_bitVector.contains(name);
        }
    }

    public void markAsBitVector(String name) {
        if(var_bitVector ==null) var_bitVector =new HashSet<String>();
        var_bitVector.add(name);
    }

    public void markAsBoolean(String name) {
        if(var_boolean ==null) var_boolean =new HashSet<String>();
        var_boolean.add(name);
    }

    public boolean isBoolean(String name) {
        if(var_boolean ==null) {
            return false;
        }
        else {
            return var_boolean.contains(name);
        }
    }

    ////////////////////////////////////////////////////////////////////////////
    public boolean isOrderSAT(String name) {
        if(ordervar_sat==null) {
            return false;
        }
        else {
            return ordervar_sat.contains(name);
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // JSON output of model

    public void writeVarDomainsAsJSON(StringBuilder bf) {
        bf.append("[");
        categoryentry c = category_first;
        boolean decisionFound = false;
        while (c != null) {
            if (c.cat == ASTNode.Decision) {
                if (decisionFound) {
                    bf.append(",");
                } else {
                    decisionFound = true;
                }
                bf.append("\n");
                ASTNode domain = getDomain(c.name);
                bf.append("{\n\"name\": \"" + escapeVar(c.name) + "\",\n");
                bf.append("\"domain\": [");
                ArrayList<Intpair> domPairs = domain.getIntervalSet();
                for (int i = 0; i < domPairs.size(); i++) {
                    bf.append("[" + domPairs.get(i).lower + ", " + domPairs.get(i).upper + "]");
                    if (i < domPairs.size() - 1) {
                        bf.append(",");
                    }
                }
                bf.append("]\n}");
            }

            c = c.next;
        }
        bf.append("]");
    }

    public void writeVarListAsJSON(StringBuilder bf) {
        bf.append("[");
        categoryentry c = category_first;
        boolean decisionFound = false;
        while (c != null) {
            if (c.cat == ASTNode.Decision) {
                if (decisionFound) {
                    bf.append(",");
                } else {
                    decisionFound = true;
                }
                bf.append("\"" + escapeVar(c.name) + "\"");
            }
            c = c.next;
        }
        bf.append("]");
    }

    String escapeVar(String s) {
        return "$" + s;
    }

    
    public static String unescapeVar(String s) {
        return s.replaceAll("^\\$(.*)$", "$1");
    }
    
    public ArrayList<String>  getVarNamesList() {
        ArrayList<String> vars = new ArrayList<String>();
        categoryentry c = category_first;
        while (c != null) {
            if (c.cat == ASTNode.Decision) {
                vars.add(c.name);
            }
            c = c.next;
        }
        return vars;
    }
}
