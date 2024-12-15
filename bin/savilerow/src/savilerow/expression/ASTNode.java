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
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;

import savilerow.*;
import savilerow.model.*;

// Abstract Syntax Tree node.

public abstract class ASTNode implements Serializable {
    public static final long serialVersionUID = 1L;
    
    ASTNode parent;
    
    int childno;    // If this node is child of another node, which child is it.
    
    /* ====================================================================
     constructor
    ==================================================================== */
    ASTNode() {
    }
    
    /* ====================================================================
     getChildren
    ==================================================================== */
    public ArrayList<ASTNode> getChildren() {
        return new ArrayList<ASTNode>();
    }
    
    public ArrayList<ASTNode> getChildren(int first) {
        return new ArrayList<ASTNode>();
    }
    
    public ASTNode[] getChildrenArray() {
        return null;
    }
    
    public ASTNode[] getChildrenArray(int startpos) {
        return null;
    }
    
    /* ====================================================================
     Get and set parent pointer. 
    ==================================================================== */

    public final ASTNode getParent() {
        return parent;
    }

    public final void setParent(ASTNode p) {
        parent = p;
    }
    
    public boolean hasModel() {
        return false;
    }
    public Model getModel() {
        assert false;
        return null;
    }
    public void setModel(Model _m) {
        assert false;
    }
    
    /* ====================================================================
     Get and set individual children -- must be used instead of accessing
     the 'children' array directly.
    ==================================================================== */

    public void setChild(int i, ASTNode c) {
        assert false;
    }
    
    public ASTNode getChild(int i) {
        assert false;
        return null;
    }
    
    //  Same as above with a promise the caller will not change the child AST. 
    public ASTNode getChildConst(int i) {
        assert false;
        return null;
    }
    
    //  Avoid children of this ASTNode being copied when this ASTNode is replaced. 
    public void detachChildren() {
    }
    
    public String toString() {
        String st = getClass().getName();
        st = st.substring(st.lastIndexOf('.') + 1);        // chop off package name
        return st + "()";
    }
    
    public int numChildren() { 
        return 0;
    }
    
    public int getChildNo() { return childno; }
    public void setChildNo(int c) { childno = c; }

    /* ====================================================================
     copy()
    ==================================================================== */
    public abstract ASTNode copy();

    /* ====================================================================
     equals()
     Deep equality.
     Must be overridden by any subclass that has its own internal state.
     For example, NumberConstant.
    ==================================================================== */
    @Override
    public boolean equals(Object b) {
        return this.getClass() == b.getClass();
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   The hashCode functions use hashCache.
    //   When the tree is changed, the hashCaches must be reset to Integer.MIN_VALUE 
    //   from the change point to the root. 
    
    @Override
    public int hashCode() {
        return (this.getClass().getName()).hashCode();
    }
    
    /* ====================================================================
     isRelation()
     Says whether an ASTNode is of bool type, or matrix of bool.
     Other possibilities are int, domain
     False by default
    ==================================================================== */
    public boolean isRelation() {
        return false;
    }

    /* ====================================================================
     isNumerical()
     Says whether an ASTNode is of type int or matrix of int. 
    ==================================================================== */
    public boolean isNumerical() {
        return false;
    }

    /* ====================================================================
     isSet()
     Says whether an ASTNode is of type (any) set, boolean set, etc. 
    ==================================================================== */
    public boolean isSet() {
        return false;
    }
    
    public boolean isBooleanSet() {
        return false;
    }
    
    public boolean isIntegerSet() {
        return isSet() && ! isBooleanSet();
    }
    
    public boolean isFiniteSet() {
        return false;
    }
    // Is it bounded above or below, for infinite sets.
    public boolean isFiniteSetUpper() {
        return false;
    }
    public boolean isFiniteSetLower() {
        return false;
    }
    
    public boolean isConstantSet() {
        return false;
    }
    
    /* ====================================================================
     Methods for commutative or associative operators like And, Or to 
     describe themselves.
     isCommAssoc()  Commutative and associative. 
     
    ==================================================================== */

    public boolean isCommAssoc() {
        return false;
    }

    /* ====================================================================
     isConstant()
     Says whether an ASTNode represents a constant value, whether arithmetic
     or boolean. getValue() gets the value.
     isConstant() is not the same as getCategory returning ASTNode.Constant,
     because isConstant only returns true when this node is a single node
     representing a constant, e.g. a NumberConstant.
    ==================================================================== */

    public boolean isConstant() {
        return false;
    }
    
    /* ====================================================================
     getValue()
     Returns the constant value of an ASTNode, representing boolean values
     as 0 or 1.
     Should only be implemented by NumberConstant, BooleanConstant ideally.
     simplify should turn a constant expression into a NumberConstant or BooleanConstant.
    ==================================================================== */

    public long getValue() {
        System.out.println("Missing getValue method: type:" + getClass().getName());
        assert false; return 0;
    }
    
    //  Methods for tuples (i.e. 1D matrices of constants) that are implemented
    //  for the general CompoundMatrix and the specialised tuple types.
    public boolean isTuple() {
        return false;
    }
    public int getTupleLength() {
        System.out.println("Missing getTupleLength method: type:" + getClass().getName());
        assert false; return 0;
    }
    
    public long getValueIdx(int idx) {
        System.out.println("Missing getValueIdx method: type:" + getClass().getName());
        assert false; return 0;
    }
    
    
    /* ====================================================================
     toFlatten(boolean propagate)
     Indicates whether this ASTNode needs to be flattened.
     Default for Minion is that any relation can be embedded in And and Or,
     and can be at the top level, otherwise it must be flattened.
     All arithmetic expressions must overload this method.
     
     Default for Gecode is that everything has to be flattened.
     Propagate parameter indicates that we are doing domain filtering, which
     means output to Minion. 
    ==================================================================== */
    
    public boolean toFlatten(boolean propagate) {
        // Never flatten variable refs, constants.
        if (this instanceof Identifier || this instanceof MatrixDeref || this instanceof SafeMatrixDeref || this instanceof MatrixSlice || 
            this.isConstant() || this instanceof Top || this instanceof SATLiteral || this instanceof FromSolution) {
            return false;
        }
        
        if (this.isRelation()) {
            ASTNode p = getParent();
            if ((CmdFlags.getFlatzinctrans() || CmdFlags.getMinizinctrans()) && !propagate) {
                // fzn/mzn backends. Flatten every relation that is not top-level by default, unless this method is overridden. 
                if (p instanceof Top || (p instanceof And && (p.getParent() instanceof Top))) {
                    return false;
                }
                return true;
            }
            else if(CmdFlags.soltype==SolEnum.MIP && !propagate) {
                // MIP backend. Do not flatten InSet, =, !=, for now. Other unary constraints to follow. 
                if (p instanceof Top || (p instanceof And && (p.getParent() instanceof Top))) {
                    return false;
                }
                // Exclude expressions that can be encoded as a sum of 0/1 variables representing values of an original variable. 
                if( (this instanceof Equals || this instanceof Less || this instanceof LessEqual || this instanceof Iff)
                    && (getChild(0).isConstant() || getChild(1).isConstant()) ) {
                    return false;
                }
                if(this instanceof InSet) {
                    return false;
                }
                if(this instanceof AllDifferent && this.getChild(0) instanceof CompoundMatrix && (this.getChild(0).getChild(1).isConstant() || this.getChild(0).getChild(2).isConstant())) {
                    return false;
                }
                if(this instanceof Negate) {
                    return false;
                }
                return true;
            }
            else if(CmdFlags.getSattrans() && !propagate && (!CmdFlags.getSMTtrans() || !willSMTEncode())) {
                // SAT. Flatten expressions that are not top-level and do not have a single literal encoding.
                if(p instanceof Top || (p instanceof And && (p.getParent() instanceof Top))) {
                    return false;
                }
                // Exclude expressions that are encoded as a single SAT literal.
                if( (this instanceof Equals || this instanceof Less || this instanceof Iff) 
                    && (getChild(0).isConstant() || getChild(1).isConstant()) ) {
                    return false;
                }
                if(this instanceof AllDifferent && this.getChild(0) instanceof CompoundMatrix && (this.getChild(0).getChild(1).isConstant() || this.getChild(0).getChild(2).isConstant())) {
                    return false;
                }
                if(this instanceof Negate) {
                    return false;
                }
                // Exclude expressions that are encoded as a single SAT literal -- particular for <=, extract (sum <= k) but not (x <= k)
                if(this instanceof LessEqual &&
                    (( getChild(0).isConstant() && getChild(1) instanceof Identifier ) || (getChild(1).isConstant() && getChild(0) instanceof Identifier) )) {
                    return false;
                }
                if(CmdFlags.use_polarity && p instanceof Implies && this.getChildNo()==1 && p.polarity()==1) {
                    return false;  //  Treat implication like ToVariable in this case. 
                }
                return true;
            }
            else if(CmdFlags.getSMTtrans() && !propagate && willSMTEncode() 
                && this instanceof Or
                && !(p instanceof Iff || p instanceof Implies)) {
                return false;
            }
            else {
                // Minion or Dominion
                if (p instanceof Top || p instanceof And || p instanceof Or               
                    || p instanceof ForallExpression || p instanceof ExistsExpression) {  // These two for class-level flattening.
                    return false;
                }
                if(p instanceof Implies && p.getChild(1)==this) {
                    return false; // Right-hand side of implication can be a constraint -- will be output as reifyimply.
                }
                return true;
            }
        } else {
            return false;            // Arithmetic expressions must override this method.
        }
    }
    
    /* ====================================================================
     toCSE()
     
     There are two reasons to eliminate something by CSE.
     
     1) It will improve propagation by transferring extra information from
        one constraint to another. e.g. x=y, cannot tell if x=y or x!=y from
        domains alone. CSE will transfer this information via an added
        boolean variable b <-> x=y. 
     
     2) To improve efficiency, e.g. in Gecode we would need to flatten 
        x=5 inside an Or. If there are multiple occurrences of x=5, we just
        want one boolean var. 
     
     Because of reason 2, this method depends on the output format.
     
    ==================================================================== */

    public final boolean toCSE() {
        // Never flatten variable refs, constants.
        if (this instanceof Identifier || this instanceof MatrixDeref || this instanceof SafeMatrixDeref 
            || this.isConstant() || this instanceof Top || this instanceof FromSolution) {
            return false;
        }
        
        if (this.getDimension() > 0) {            // No matrices
            return false;
        }
        
        if (this.isNumerical()) {
            // Numerical expression that is not a constant, identifier or matrixderef
            return true;
        }
        
        if (this.isRelation()) {
            // Relation expression that is not a constant, identifier or matrixderef
            
            if(CmdFlags.getFlatzinctrans()) {
                return true;
            }
            else {   
                if(CmdFlags.getSattrans()) {
                    // Anything represented by a single SAT literal should not be extracted by CSE.
                    if( (this instanceof Equals || this instanceof Less || this instanceof LessEqual || this instanceof Iff) 
                        && (getChild(0).isConstant() || getChild(1).isConstant()) ) {
                        return false;
                    }
                    if(this instanceof Negate) {
                        return false;   // No benefit to extracting negation in SAT. 
                    }
                    if(this instanceof AllDifferent && this.getChild(0) instanceof CompoundMatrix && (this.getChild(0).getChild(1).isConstant() || this.getChild(0).getChild(2).isConstant())) {
                        return false;
                    }
                }
                else {
                    // For Minion and Dominion, constraints can be nested in And or Or, and
                    // in some cases there is never a benefit to doing CSE (i.e. unary cts)
                    // For Minizinc, follow output for Minion as closely as possible. 
                    
                    if(this instanceof Negate && getChild(0) instanceof Identifier) {
                        // Negation of a variable is supported in Minion with a mapper.
                        return false;
                    }
                    
                    if(this.getParent() instanceof And || this.getParent() instanceof Or) {
                        // Binary constraints with a constant.
                        if( (this instanceof Equals || this instanceof Less || this instanceof LessEqual || this instanceof Iff) 
                            && (getChild(0).isConstant() || getChild(1).isConstant()) ) {
                            return false;
                        }
                        if(this instanceof AllDifferent && this.getChild(0) instanceof CompoundMatrix && (this.getChild(0).getChild(1).isConstant() || this.getChild(0).getChild(2).isConstant())) {
                            return false;
                        }
                        
                        // Unary constraints
                        if(this instanceof InSet) {
                            return false;
                        }
                    }
                }
                
                return true;
            }
        }

        return false;        // Catch all other types
    }
    
    /* ====================================================================
     typecheck()
     Classes may override this method to provide type/dimension 
     checking.
    ==================================================================== */
    
    public boolean typecheck(SymbolTable st) {
        for (int i =0; i < numChildren(); i++) {
            if (!this.getChild(i).typecheck(st)) {
                return false;
            }
        }
        return true;
    }
    
    //  Second pass of typechecking, after removal of matrices indexed by
    //  matrices. 
    
    public boolean typecheck2(SymbolTable st) {
        for (int i=0; i<numChildren(); i++) {
            if (!this.getChild(i).typecheck2(st)) {
                return false;
            }
        }
        return true;
    }
    
    /* ====================================================================
     getCategory()
     Returns 0,1,2,3 for Constant, Parameter, Quantifier, Decision
     Category depends on the Identifiers present in the tree, and it's the 
     highest one of those.
     Overloaded by Identifier only.
     Undeclared indicates an expression contains an id that has not been declared above.
    ==================================================================== */

    public static final int Constant =0;
    public static final int Parameter =1;
    public static final int Quantifier =2;
    public static final int Decision =3;

    // Not distinct categories, but contained in symbol table
    public static final int Auxiliary =10;
    public static final int ConstantMatrix =11;
    
    public static final int Undeclared =20;

    public int getCategory() {
        int cat = ASTNode.Constant;
        for (int i =0; i < numChildren(); i++) {
            int child_cat = getChild(i).getCategory();
            if (child_cat > cat) {
                cat = child_cat;
            }
        }
        return cat;
    }

    // Return the dimension of the expression. Most things are 0, matrices
    // and matrix slices, 'flatten' etc must override this function
    public int getDimension() {
        return 0;
    }
    
    // For matrix types, are the index domains known to be uniform.
    // May return false when the answer is unknown. 
    // For example, may return false for matrix comprehensions that later become matrix literals that are regular.
    public boolean isRegularMatrix() {
        return false;   ///  Not a matrix type.
    }
    
    //  Does this node have the structure of a matrix literal, i.e. 
    //  CompoundMatrix or EmptyMatrix down to the leaves.  
    public boolean isMatrixLiteral() {
        return false;
    }
    
    // For indexable expressions, return the domain of each dimension.
    public ArrayList<ASTNode> getIndexDomains() {
        return null;
    }
    
    // Slower version for irregular matrices.
    public ArrayList<ASTNode> getIndexDomainsIrregular() {
        return null;
    }

    // Generic simplify for the children that don't implement it.
    // Returns null if no change is to be made. 
    public ASTNode simplify() {
        return null;
    }
    
    // Gets a list of Intpair for set types.
    // Infinites are represented using Long.MIN_VALUE and Long.MAX_VALUE.
    // May return null if it is not possible to obtain the interval set. 
    public ArrayList<Intpair> getIntervalSet() {
        if (this.isConstant()) {
            ArrayList<Intpair> i = new ArrayList<Intpair>();
            i.add(new Intpair(this.getValue(), this.getValue()));
            return i;
        } else {
            return null;
        }
    }
    
    // Gets a list of intpair for numerical or boolean expressions.
    // May over-estimate the true set of possible values.
    public ArrayList<Intpair> getIntervalSetExp() {
        ArrayList<Intpair> i = new ArrayList<Intpair>();
        i.add(this.getBounds());
        return i;
    }
    
    //  Returns an interval enclosing all the values of an integer/boolean
    //  expression,  enclosing all the values of a set,
    //  or for a matrix it encloses the union of all the bounds of the things in the matrix.
    //  Conventions: Long.MIN_VALUE is -inf and Long.MAX_VALUE is +inf.
    //  Typically returns 1..0 if no values are possible. 
    public Intpair getBounds() {
        if (this.isConstant()) {
            long i = this.getValue();
            return new Intpair(i, i);
        } else if (this.isRelation()) {
            return new Intpair(0,1);
        } else {
            if (CmdFlags.getBvTraversal()) { return null; }
            System.out.println("Missing getBounds method for type:"+ getClass().getName());
            assert false;
            return new Intpair(Long.MIN_VALUE, Long.MAX_VALUE);
        }
    }
    
    public boolean exceedsBoundThreshold() {
        Intpair a = this.getBounds();
        return a.upper - a.lower + 1 > Constants.boundvar_threshold;
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // Output methods
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException {
        System.out.println("Missing toMinion method. type:" + getClass().getName()+" instance:"+this);
        assert false;
    }
    
    public void toMinionWithAuxVar(BufferedWriter b, ASTNode auxvar) throws IOException {
        System.out.println("Missing toMinionWithAuxVar method. type:" + getClass().getName());
        assert false;
    }
    
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        System.out.println("Missing toFlatzinc method. type:" + getClass().getName());
        assert false;
    }
    public void toFlatzincWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException {
        System.out.println("Missing toFlatzincWithAuxVar method. type:" + getClass().getName());
        assert false;
    }
    
    public void toMinizinc(StringBuilder b, boolean bool_context) {        /// context-- is it expecting a bool.
        System.out.println("Missing toMinizinc method. type:" + getClass().getName());
        assert false;
    }
    
    public void toMIP(BufferedWriter b) throws IOException {
        System.out.println("Missing toMIP method. type:" + getClass().getName());
        assert false;
    }
    
    public Long toSATLiteral(Sat satModel) {
        return null;
    }
    
    public void toSAT(Sat satModel) throws IOException {
        if (!(this instanceof Top)) {
            CmdFlags.errorExit("Missing toSAT method. type:" + getClass().getName());
        }
        getChild(0).toSAT(satModel);
    }

    public void toSMT(SMT satModel) throws IOException {
        toSAT(satModel);
    }

    // Returns true if this node can be encoded into SMT (without using the SAT encoding)
    public boolean usesSMTEncoding() {
        // By default, no node uses integer encoding (since that is how it originally worked for SAT solvers)
        return false;
    }

    // Returns true if this node will be encoded into SMT. The difference with usesSMTEncoding is that this checks
    // the parents to see if they can be encoded into SMT as well, while usesSMTEncoding only checks the children.
    // This means that this method will only return true if it will be SMT in the final output, while
    // usesSMTEncoding will return true if it can be used as such
    public boolean willSMTEncode() {
        // By default, only willSMTEncode if it can be encoded int SMT and its parent willSMTEncode (recursive)
        return usesSMTEncoding() && (getParent() == null || getParent().willSMTEncode());
    }

    // Returns true if this node is a valid IDL encoding or if it can be part of one
    public boolean canIDLEncode() {
        // By default, no node can encode into IDL
        return false;
    }

    // Returns true if this node can be encoded as a single variable in SMT
    public boolean canVariableEncode() {
        // By default, no node can't be represented as a single variable
        return false;
    }
    
    public void toSATWithAuxVar(Sat satModel, long aux) throws IOException {
        CmdFlags.errorExit("Missing toSATWithAuxVar(long) method. type:" + getClass().getName()+" "+this+" "+this.getParent());
    }
    public void toSATWithAuxVar(Sat satModel, ASTNode auxVar) throws IOException {
        CmdFlags.errorExit("Missing toSATWithAuxVar(AST) method. type:" + getClass().getName()+" "+this+" "+this.getParent());
    }
    
    /* ====================================================================
     normalise()
     Sorts the expression to reveal more CSE's. Should be simplified first.
     Called by TransformNormalise
    ==================================================================== */
    public ASTNode normalise() {
        return this;
    }
    
    public ASTNode normaliseAlpha() {
        return null;
    }
    
    // Comparator to sort by hashcode
    // Note: this comparator imposes orderings that are inconsistent with equals.
    static class cmphash implements Comparator<ASTNode> {
        public int compare(ASTNode x, ASTNode y) {
            int xhash=x.hashCode();
            int yhash=y.hashCode();
            if(xhash<yhash) {
                return -1;
            }
            else if(xhash==yhash) {
                return 0;
            }
            else {
                return 1;
            }
        }
    }
    
    //  Sort ArrayList by hashcode, return whether order changed. 
    public static boolean sortByHashcode(ArrayList<ASTNode> ch) {
        boolean changed=false;
        //  Is it out of order?
        for (int i =0; i < ch.size()-1; i++) {
            if(ch.get(i).hashCode()>ch.get(i+1).hashCode()) {
                changed=true;
                break;
            }
        }
        
        if(!changed) {
            return false;
        }
        
        Collections.sort(ch, new cmphash());
        return changed;
    }
    
    // Comparator to sort by string comparison
    static class cmpstring implements Comparator<ASTNode> {
        public int compare(ASTNode x, ASTNode y) {
            String stx=x.toString();
            String sty=y.toString();
            return stx.compareTo(sty);
        }
    }
    
    public static boolean sortByAlpha(ArrayList<ASTNode> ch) {
        boolean changed=false;
        //  Is it out of order?
        for (int i =0; i < ch.size()-1; i++) {
            if(ch.get(i).toString().compareTo(ch.get(i+1).toString())>0) {
                changed=true;
                break;
            }
        }
        
        if(!changed) {
            return false;
        }
        
        Collections.sort(ch, new cmpstring());
        return changed;
    }
    
    /* ====================================================================
     isDetached()
     Has this ASTNode been cut out of the tree.
     Assumes parent pointers are still intact.
    ==================================================================== */
    public boolean isDetached() {
        ASTNode c=this;
        ASTNode p=parent;
        
        while(p!=null) {
            if(p.getChild(c.childno)!=c) {
                return true;
            }
            c=p;
            p=p.parent;
        }
        return false;
    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // Goes up the tree looking for an object that will define the domain for
    // an identifier. Either a quantifier or a MatrixDomain at present, but may be
    // extended.
    public ASTNode getDomainForId(ASTNode id) {
        if (getParent() != null) {
            return getParent().getDomainForId(id);
        } else {
            return null;
        }
    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // Is the node part of the top-level conjunction? e.g. is it a forall quantifier that
    // is contained in another forall, that is in the top-level And?

    // And, Forall and Top should override this method.

    public boolean inTopConjunction() {
        return false;
    }

    // Similar to above but does not include expressions inside a Forall
    // Should be overridden by And and Top only.
    public boolean inTopAnd() {
        return false;
    }

    // Check if an expression is unary. For now, I'll just say it has one Identifier or MatrixDeref in it in total.
    public boolean unary() {
        if (this instanceof Identifier || this instanceof MatrixDeref || this instanceof SafeMatrixDeref) {
            return true;
        }
        boolean seenunary = false;
        for (int i =0; i < numChildren(); i++) {
            if (getChild(i).unary()) {
                if (seenunary) {
                    return false;
                }
                seenunary = true;
            } else if (! getChild(i).isConstant()) {
                return false;
            }
        }
        return seenunary;
    }

    // Check if a set type (e.g. a domain) contains a particular value.
    public boolean containsValue(long val) {
        if (this.isConstant()) {
            return val == this.getValue();
        }

        System.out.println("Missing containsValue method. type:" + getClass().getName());
        assert false;
        return false;
    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // Does this tree contain another?
    public boolean contains(ASTNode in) {
        if (this.equals(in)) {
            return true;
        } else {
            for (int i =0; i < numChildren(); i++) {
                if (getChild(i).contains(in)) {
                    return true;
                }
            }
        }
        return false;
    }
    
    public int treesize() {
        // count nodes
        int siz =1;
        for (int i =0; i < numChildren(); i++) {
            siz = siz + getChild(i).treesize();
        }
        return siz;
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //  Is it a constraint that gets 'strong propagation'?
    //  Defined also for parts of constraints -- whether they can be extracted
    //  to a constraint that gets 'strong' propagation. 
    public boolean strongProp() {
        return isConstant();
    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // Does this tree contain an auxiliary variable?
    public boolean containsAux() {
        if(this instanceof Identifier && ((Identifier)this).m.global_symbols.category.get(this.toString()).cat==ASTNode.Auxiliary) {
            return true;
        }
        else {
            for (int i=0; i < numChildren(); i++) {
                if (getChild(i).containsAux()) {
                    return true;
                }
            }
        }
        return false;
    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // 
    // Deal with negation.

    // Does it implement the negation method.
    public boolean isNegatable() {
        return false;
    }

    // Return the negation of this constraint/expression.
    public ASTNode negation() {
        System.out.println("negation method not implemented:" + getClass().getName());
        assert false;
        return null;
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //  Construct ArrayLists (saves some typing)
    
    public static ArrayList<ASTNode> list() {
        return new ArrayList<ASTNode>();
    }
    public static ArrayList<ASTNode> list(ASTNode a) {
        ArrayList<ASTNode> l=new ArrayList<ASTNode>();
        l.add(a);
        return l;
    }
    public static ArrayList<ASTNode> list(ASTNode a, ASTNode b) {
        ArrayList<ASTNode> l=new ArrayList<ASTNode>();
        l.add(a); l.add(b);
        return l;
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //  Mainly for SAT ecnoding. 
    public boolean test(long value1, long value2, long value3) {
        CmdFlags.errorExit("Missing test method. type:" + getClass().getName());
        return false;
    }
    public boolean test(long value1, long value2) {
        CmdFlags.errorExit("Missing test method. type:" + getClass().getName());
        return false;
    }
    public boolean test(long value1) {
        CmdFlags.errorExit("Missing test method. type:" + getClass().getName());
        return false;
    }
    
    //  Ternary functional constraints.
    public long func(long value1, long value2) {
        CmdFlags.errorExit("Missing func method. type:" + getClass().getName());
        return 0;
    }
    
    //   Returns true iff the node can be encoded with directEncode or orderEncode methods. 
    public boolean hasLiteralEncoding() {
        return false;
    }
    public long directEncode(Sat satModel, long value) {
        CmdFlags.errorExit("Missing directEncode method. type:" + getClass().getName());
        return 0;
    }
    public long orderEncode(Sat satModel, long value) {
        CmdFlags.errorExit("Missing orderEncode method. type:" + getClass().getName());
        return 0;
    }
    
    public String smtEncodeBool(SMT satModel) {
        CmdFlags.errorExit("Missing smtEncodeBool method. type:" + getClass().getName());
        return null;
    }
    public String smtEncodeInt(SMT satModel) {
        CmdFlags.errorExit("Missing smtEncodeInt method. type:" + getClass().getName());
        return null;
    }
    public String smtEncodeBV(SMT satModel) {
        CmdFlags.errorExit("Missing smtEncodeBV method. type:" + getClass().getName());
        return null;
    }
    
    //  How this expression bounds its child:
    //  bounds it below (pushes it up)    +1
    //  bounds it above (pushes it down)  -1
    //  mixed, punches holes, or unknown   0
    //  e.g. minimising statement bounds above (-1)
    public int polarity(int child) {
        return 0;
    }
    //  Polarity of this node. 
    public int polarity() {
        if(getParent()==null) {
            return 1;  //  Assume a constraint that will be attached to the top-level conjunction. 
        }
        return getParent().polarity(getChildNo());
    }
    
    /** Get basic JSON information on node (name, symmetry of children)
     * @param includeComma - whether to include a comma after the last member i.e. it is not the last
     *@return string containing json code for an object (object is not closed to allow easy adition of members)
     */
    public void toJSONHeader(StringBuilder bf, boolean includeComma) {
        String name = this.getClass().getName();
        name = name.substring(name.lastIndexOf('.') + 1);
        bf.append("{\n\"type\": \"");
        bf.append(name);
        bf.append("\"");
        
        if (numChildren() > 0) {
            bf.append(",\n\"symmetricChildren\": " + childrenAreSymmetric());
        }
        
        if (includeComma) {
            bf.append(",\n");
        } else {
            bf.append("\n");
        }
    }
    
    public void toJSON(StringBuilder bf) {
        toJSONHeader(bf, true);
        // children
        bf.append("\"Children\": [");
        for (int i = 0; i < numChildren(); i++) {
            bf.append("\n");
            getChild(i).toJSON(bf);
            // not last child
            if (i < numChildren() - 1) {
                bf.append(",");
            }
        }
        bf.append("]\n}");
    }
    
    public boolean childrenAreSymmetric() {
        return false;
    }
    
    public boolean isChildSymmetric(int childIndex) {
        return false;
    }
    
    public boolean isMyOnlyOtherSiblingEqualZero(int childIndex) {
        if (numChildren() != 2) {
            return false; 
        }
        else {
            ASTNode node;
            if (childIndex == 0) {
                node = getChild(1);
            }
            else {
                node = getChild(0);
            }
            return node instanceof NumberConstant && node.getValue() == 0;
        }
    }
    
    public boolean canChildBeConvertedToDifference(int childIndex) {
        return false;
    }
}
