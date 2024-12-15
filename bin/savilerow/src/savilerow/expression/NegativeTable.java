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

import savilerow.CmdFlags;
import savilerow.model.*;

public class NegativeTable extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    protected transient Model m;
    
    public NegativeTable(Model _m, ASTNode v, ASTNode tups)
    {
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
	    return new NegativeTable(m, getChild(0), getChild(1));
	}
	public boolean isRelation(){return true;}
	public boolean strongProp() {
        return getChild(0).strongProp();
    }
	
	public boolean typecheck(SymbolTable st) {
	    if(!getChild(0).typecheck(st)) return false;
	    if(!getChild(1).typecheck(st)) return false;
	    
	    if(getChild(0).getDimension()!=1) {
            CmdFlags.println("ERROR: First argument of negativetable should be 1-dimensional matrix: "+this);
            return false;
        }
	    if(getChild(1).getDimension()!=2) {
	        CmdFlags.println("ERROR: Second argument of negativetable should be 2-dimensional matrix: "+this);
            return false;
	    }
	    
        return true;
    }
    
    public ASTNode simplify() {
        ASTNode c0=getChildConst(0);
        if((c0 instanceof CompoundMatrix || c0 instanceof EmptyMatrix) && (getChild(1).getCategory()==ASTNode.Constant)) {
            ASTNode table=getChildConst(1);
            if(table==getChild(1) && (table instanceof CompoundMatrix || table instanceof EmptyMatrix)) {
                // Also of category constant, must be a matrix literal. 
                
                if(table instanceof EmptyMatrix) {
                    return new BooleanConstant(true);
                }
                
                // Make an identifier for it and store elsewhere.
                
                // Store table in deduplicated store.
                ASTNode tabid=m.cmstore.newConstantMatrixDedup(table);
                getChild(0).setParent(null);
                return new NegativeTable(m, getChild(0), tabid);
            }
            
            if(table instanceof CompoundMatrix || table instanceof EmptyMatrix) {
                // Both vars and table are matrix types we can work with. 
                if(table instanceof EmptyMatrix) {
                    // It's an empty vector of tuples, not a vector containing a single empty tuple.
                    // Constraint is always satisfied.
                    return new BooleanConstant(true);
                }
                
                if(c0 instanceof EmptyMatrix) {
                    // ... and table is non-empty, i.e. contains one disallowed tuple of length 0. 
                    return new BooleanConstant(false);
                }
                
                ArrayList<ASTNode> vars=c0.getChildren(1);
                
                // Simple one -- just project out assigned variables. 
                for(int i=0; i<vars.size(); i++) {
                    if(vars.get(i).isConstant()) {
                        long val=vars.get(i).getValue();
                        vars.remove(i);
                        
                        // Filter the table.
                        ArrayList<ASTNode> newtab=new ArrayList<ASTNode>();
                        for(int j=1; j<table.numChildren(); j++) {
                            ASTNode tuple=table.getChildConst(j);
                            if( ! (tuple instanceof CompoundMatrix)) {
                                //  Delay. The tuple is unknown -- e.g. a matrix comprehension.
                                return null;
                            }
                            if(tuple.getChild(i+1).getValue() == val) {
                                ArrayList<ASTNode> tmp=table.getChildConst(j).getChildren(1);
                                tmp.remove(i);  // Get rid of the column i
                                
                                newtab.add(CompoundMatrix.make(tmp));
                            }
                        }
                        if(c0 == getChild(0)) {
                            for(int j=0; j<vars.size(); j++) {
                                vars.get(i).setParent(null);
                            }
                        }
                        return new NegativeTable(m, CompoundMatrix.make(vars), CompoundMatrix.make(newtab));
                    }
                }
            }
        }
        return null;
    }
    
    @Override
    public boolean isNegatable() {
        return true;
    }
    @Override
    public ASTNode negation() {
        return new Table(m, getChild(0), getChild(1));
    }
    
    public String toString() {
        return generic_to_string("!table");
    }
    
	public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    b.append("negativetable(");
	    getChild(0).toMinion(b, false);
	    b.append(", ");
	    if(getChild(1) instanceof CompoundMatrix || getChild(1) instanceof EmptyMatrix) {
	        ArrayList<ASTNode> tups=getChild(1).getChildren();
	        b.append("{");
            for(int i=1; i<tups.size(); i++)
            {
                ArrayList<ASTNode> elements=tups.get(i).getChildren();
                b.append("<");
                for(int j=1; j<elements.size(); j++)
                {
                    elements.get(j).toMinion(b, false);
                    if(j<elements.size()-1) b.append(", ");
                }
                b.append(">");
                
                if(i<tups.size()-1) b.append(", ");
            }
            b.append("}");
	    }
	    else {
	        getChild(1).toMinion(b, false);
	    }
	    b.append(")");
	}
	
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
	    b.append("constraint table_int_reif(");
	    getChild(0).toFlatzinc(b, false);
	    b.append(",[");
	    ASTNode cmat=getChildConst(1);
	    
	    for(int i=1; i<cmat.numChildren(); i++) {
            for(int j=1; j<cmat.getChild(i).numChildren(); j++) {
                cmat.getChild(i).getChild(j).toFlatzinc(b, false);
                b.append(",");
            }
        }
        
        b.append("], false);");
	}
	
	public void toMinizinc(StringBuilder b, boolean bool_context) {
	    b.append("(not table(");
	    getChild(0).toMinizinc(b, false);
	    b.append(",");
	    if(getChild(1) instanceof CompoundMatrix || getChild(1) instanceof EmptyMatrix) {
	        // Print out very strange Minizinc 2d array format.
	        b.append("[");
	        for(int i=1; i<getChild(1).numChildren(); i++) {
	            ASTNode ch=getChild(1).getChild(i);
	            b.append("| ");
	            for(int j=1; j<ch.numChildren(); j++) {
	                ch.getChild(j).toMinizinc(b, false);
	                if(j< ch.numChildren()-1) b.append(",");
	            }
	        }
	        b.append("|]");
	    }
	    else {
	        getChild(1).toMinizinc(b, false);
	    }
	    b.append("))");
	}
	
	public void toSAT(Sat satModel) throws IOException {
        ASTNode vars = getChild(0);
        ASTNode tab=getChildConst(1);
        
        // Direct encoding.
        
        for (int i =1; i < tab.numChildren(); i++) {
            ArrayList<Long> cl=new ArrayList<Long>();
            
            for(int j=1; j<tab.getChild(i).numChildren(); j++) {
                long lit=vars.getChild(j).directEncode(satModel, tab.getChild(i).getChild(j).getValue());
                cl.add(-lit);
            }
            satModel.addClause(cl);
        }
    }
    
    public void toSATWithAuxVar(Sat satModel, long reifyVar) throws IOException {
        ASTNode vars = getChild(0);
        ASTNode tab=getChildConst(1);
        
        ArrayList<Long> newVars=new ArrayList<Long>();
        
        for (int i =1; i < tab.numChildren(); i++) {
            ArrayList<Long> cl=new ArrayList<Long>();
            
            for(int j=1; j<tab.getChild(i).numChildren(); j++) {
                long lit=vars.getChild(j).directEncode(satModel, tab.getChild(i).getChild(j).getValue());
                cl.add(-lit);   //  Positive literals, unlike the direct encoding above. 
            }
            
            Long auxVar = satModel.createAuxSATVariable();
            newVars.add(auxVar);
            
            satModel.addClauseReified(cl, -auxVar);
            //  Literals negative and auxVar also negative.
            // Hence if auxVar is 1 then all literals must be set. 
        }
        
        // If reifyVar is true, we need all the newvars to be 0.
        // else, we need one of the newvars to be 1
        satModel.addClauseReified(newVars, -reifyVar);
    }
}
