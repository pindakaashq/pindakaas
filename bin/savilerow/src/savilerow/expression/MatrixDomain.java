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


import java.util.ArrayList;

import savilerow.CmdFlags;
import savilerow.model.SymbolTable;

public class MatrixDomain extends Domain
{
    public static final long serialVersionUID = 1L;
    // First child is the base i.e. the domain of the variables in the matrix.
    // Second is an Container of identifiers for the indices.
    // Third is a condition or And of conditions
    // Other children are finite sets for the indices of the matrix
    
    public MatrixDomain(ASTNode b, ArrayList<ASTNode> i) {
        ArrayList<ASTNode> ch=new ArrayList<ASTNode>();
        ch.add(b); 
        ch.add(new Container(new ArrayList<ASTNode>()));
        ch.add(new BooleanConstant(true));
        ch.addAll(i);
        // isSet covers all non-matrix domains, incl union, intersect etc.
        // Moved to typechecking. 
        //for(ASTNode indexdom : i) assert indexdom.isSet();
        setChildren(ch);
    }
    
    public MatrixDomain(ASTNode b, ArrayList<ASTNode> i, ASTNode q_id, ASTNode conds)
    {
        assert q_id.numChildren()==i.size() || q_id.numChildren()==0;
        assert q_id instanceof Container;
        ArrayList<ASTNode> ch=new ArrayList<ASTNode>();
        ch.add(b);
        ch.add(q_id);
        ch.add(conds);
        ch.addAll(i);
        setChildren(ch);
    }
    
	public ASTNode copy() {
	    ArrayList<ASTNode> d=getChildren();
	    ArrayList<ASTNode> indices=new ArrayList<ASTNode>(d.subList(3, d.size()));
	    return new MatrixDomain(getChild(0), indices, getChild(1), getChild(2));
	}
	
	@Override
    public ASTNode getDomainForId(ASTNode id) {
        if(getChild(1).getChildren().indexOf(id)>-1) {
            return getChild(getChild(1).getChildren().indexOf(id)+3);   // index into indices domains.
        }
        else {
            if(getParent()==null) return null;
            return getParent().getDomainForId(id);  // continue up the tree.
        }
    }
	
	public ArrayList<ASTNode> getMDIndexDomains()
	{
	    ArrayList<ASTNode> indices=new ArrayList<ASTNode>();
	    for(int i=3; i<numChildren(); i++) {
	        indices.add(getChild(i));   // Shallow copy
	    }
	    return indices;
	}
	
	public ASTNode getBaseDomain()
	{
	    return getChild(0);
	}
	
	public boolean typecheck(SymbolTable st) {
	    for(int i=0; i<numChildren(); i++) {
	        if(!getChild(i).typecheck(st)) return false;
	    }
	    // This is after substitution of lettings, so everything should be a 
	    // domain.
	    for(int i=3; i<numChildren(); i++) {
	        ASTNode a=getChild(i);
	        if(!(a instanceof MatrixDomain) && !(a.isSet())) {
	            CmdFlags.println("ERROR: Expected domain in matrix domain, found: "+a);
	            return false;
	        }
	        if(!(a instanceof MatrixDomain)) {
	            //  A simple domain: may be either a finite domain or int 
	            if(! a.equals(new IntegerDomain(new Range(null,null))) && !(a.isFiniteSet())) {
	                CmdFlags.println("ERROR: Expected finite domain in matrix domain, found: "+a);
	                return false;
	            }
	        }
	        if(a.getCategory()>ASTNode.Quantifier) {
	            CmdFlags.println("ERROR: Expected no decision variables in index domain of matrix domain: "+a);
	            return false;
	        }
	    }
	    for(int i=0; i<getChild(2).numChildren(); i++) {
	        ASTNode a=getChild(2).getChild(i);
	        if(!a.isRelation() || a.getCategory()>ASTNode.Quantifier) {
	            CmdFlags.println("ERROR: Expected relational quantifier expression in conditions of matrix domain.");
	            return false;
	        }
	    }
	    return true;
	}
	
	public boolean typecheck_in_given(SymbolTable st) {
	    // Might be int(1..p) in indices with undefined p. 
	    // Don't check indices here. 
	    for(int i=0; i<3; i++) {
	        if(!getChild(i).typecheck(st)) return false;
	    }
	    
	    if(getChild(0) instanceof Identifier) {
	        CmdFlags.println("ERROR: Expected domain in matrix domain, found: "+getChild(0));
            return false;
	    }
	    
	    // Indices
	    for(int i=3; i<numChildren(); i++) {
	        ASTNode a=getChild(i);
	        if(a instanceof Identifier) {
	            CmdFlags.println("ERROR: Expected domain in matrix domain, found: "+a);
	            return false;
	        }
	    }
	    return true;
	}
	
	//  How deep is the stack of MatrixDomains?
	//  For checking that finds have at most 2, comprehension/quantifier domains and givens have at most 1. 
	public int nesting() {
	    int n=0;
	    for(int i=3; i<numChildren(); i++) {
	        if(getChild(i) instanceof MatrixDomain) {
	            int n2=((MatrixDomain)getChild(i)).nesting();
	            if(n2>n) n=n2;
	        }
	    }
	    return n+1;
	}
	
	public String toString() {
	    ArrayList<ASTNode> dim_id=getChild(1).getChildren();
	    
	    String stuff="";
	    for(int i=3; i<numChildren(); i++) {
	        stuff+=getChild(i);
	        if(i<numChildren()-1) stuff+=",";
	    }
	    String conds=getChild(2).toString();
	    
	    String out="matrix indexed by ["+stuff+"] of "+getChild(0);
	    
	    if(! conds.equals("true")) out+=" with indices "+dim_id+" and conditions "+conds;
	    return out;
	}
}
