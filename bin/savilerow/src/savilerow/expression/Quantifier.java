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


import savilerow.CmdFlags;
import savilerow.model.SymbolTable;

// Base class for forall, exists and quantified sum.
// First child is a single identifier.
// Second child is a domain
// Third child is the contained expression.
// Fourth child is conditions attached to the quantifier.

abstract public class Quantifier extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public Quantifier(ASTNode i, ASTNode d, ASTNode e) {
        super(i, d, e);
        assert i instanceof Identifier;
    }
    
    @Override
    public ASTNode getDomainForId(ASTNode id) {
        if(getChild(0).equals(id)) {
            return getChild(1);
        }
        else {
            if(getParent()==null) return null;
            return getParent().getDomainForId(id);  // continue up the tree.
        }
    }
    
    @Override
    public boolean typecheck(SymbolTable st) {
        // Recurse down the tree.
        if(!getChild(0).typecheck(st) || !getChild(1).typecheck(st) || !getChild(2).typecheck(st)) {
            return false;
        }
        
        if(getChild(1).getCategory()>ASTNode.Quantifier) {
            System.out.println("ERROR: In quantifier: "+this); 
            System.out.println("ERROR: Decision variable in quantifier domain.");
            return false;
        }
        
        // Check scoping of the identifier.
        ASTNode id=getChild(0);
        if( !(id instanceof Identifier) ) {
            System.out.println("ERROR: In quantifier: "+this); 
            System.out.println("ERROR: Item in identifier list `"+id+"' is not an identifier.");
            System.out.println("ERROR: This can occur if it was replaced when substituting in parameters.");
            return false;
        }
        if(st.hasVariable(id.toString()) || ( getParent()!=null && getParent().getDomainForId(id)!=null ) ){
            System.out.println("ERROR: In quantifier: "+this); 
            System.out.println("ERROR: Identifier `"+id+"' is already defined.");
            return false;
        }
        if(getChild(1).contains(id)) {
            System.out.println("ERROR: In quantifier: "+this); 
            System.out.println("ERROR: Quantifier domain contains the quantifier variable.");
            return false;
        }
        if(!getChild(2).contains(id)) {
            CmdFlags.warning("Expression contained in quantifier does not contain quantifier variable: "+this);
        }
        
        ASTNode dom=getChild(1);
        if( ! ( dom.isFiniteSet() || dom instanceof MatrixDomain )) {
            System.out.println("ERROR: In quantifier: "+this); 
            System.out.println("ERROR: Expected finite domain or matrix domain.");
            return false;
        }
        if(dom instanceof MatrixDomain) {
            if(((MatrixDomain)dom).nesting()>1) {
                System.out.println("ERROR: matrix indexed by matrix not allowed in quantifier: "+getChild(1));
                return false;
            }
        }
        if(getChild(2).getDimension()>0) {
            System.out.println("ERROR: quantifier (forAll, exists or sum) contains matrix: "+getChild(2));
            return false;
        }
        if(this instanceof QuantifiedSum) {
            // Should be relational or numerical
            if(!getChild(2).isRelation() && !getChild(2).isNumerical()) {
                System.out.println("ERROR: quantified sum contains expression that is not Boolean or integer: "+getChild(2));
                return false;
            }
        }
        else {
            if(!getChild(2).isRelation()) {
                System.out.println("ERROR: exists or forAll contains non-Boolean expression: "+getChild(2));
                return false;
            }
        }
        
        return true;
    }
}

