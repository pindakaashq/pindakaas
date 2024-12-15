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
import java.util.HashSet;

import savilerow.TabulationUtils;
import savilerow.model.*;

public class Or extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
	public Or(ArrayList<ASTNode> ch) {
		super(ch);
	}
	
	public Or(ASTNode[] ch) {
		super(ch);
	}
	

	public Or(ASTNode l, ASTNode r) {
	    super(l, r);
	}
	
	public Or(ASTNode a, ASTNode b, ASTNode c) {
	    super(a, b, c);
	}
	
	public ASTNode copy()
	{
	    return new Or(getChildrenArray());
	}
	public boolean isRelation(){return true;}
	public boolean strongProp() {
        for(int i=0; i<numChildren(); i++) {
            if(!getChild(i).strongProp()) {
                return false;
            }
        }
        
        //  Check for overlapping scopes. 
        HashSet<ASTNode> variableSet=new HashSet<>();
        variableSet.addAll(TabulationUtils.getVariablesOrdered(getChild(0)));
        for(int i=1; i<numChildren(); i++) {
            ArrayList<ASTNode> vars=TabulationUtils.getVariablesOrdered(getChild(i));
            for(int j=0; j<vars.size(); j++) {
                if(variableSet.contains(vars.get(j))) {
                    // Overlapping scopes, will not get GAC
                    return false;
                }
            }
            variableSet.addAll(vars);
        }
        
        return true;
    }
    
	public ASTNode simplify()
	{
	    
        boolean changed=false;
        
        ArrayList<ASTNode> ch=getChildren();
        for(int i=0; i<ch.size(); i++)
        {
            if(ch.get(i) instanceof Or) {
                changed=true;
                ASTNode curnode=ch.remove(i);
                i--;  // current element removed so move back in list.
                // Add children to end of this list, so that the loop will process them.
                ch.addAll(curnode.getChildren());
            }
        }
        
        // Constant folding
        for(int i=0; i<ch.size(); i++)
        {
            if(ch.get(i).isConstant())
            {
                long val=ch.get(i).getValue();
                if(val==1)
                {   // Found a true in the disjunction
                    return new BooleanConstant(true);
                }
                else
                {
                    changed=true;
                    ch.remove(i);
                    i--;
                }
            }
        }
        
        // Remove duplicates
        HashSet<ASTNode> a=new HashSet<ASTNode>(ch);
        if(a.size() < ch.size()) {
            changed=true;
            ch.clear();
            ch.addAll(a);
        }
        
        if(ch.size()==0) return new BooleanConstant(false); 
        if(ch.size()==1) return ch.get(0);
        if(changed) {
            for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
            return new Or(ch);
        }
        return null;
	}
	
	//  If contained in a Negate, push the negation inside using De Morgens law. 
	@Override
	public boolean isNegatable() {
	    return true;
	}
	@Override
	public ASTNode negation() {
	    ArrayList<ASTNode> newchildren=new ArrayList<ASTNode>();
	    
        for(int i=0; i<numChildren(); i++) {
            newchildren.add(new Negate(getChild(i)));
        }
        
        return new And(newchildren);
	}
	
	public boolean typecheck(SymbolTable st) {
	    for(ASTNode child :  getChildren()) {
	        if(!child.typecheck(st))
	            return false;
	        if(!child.isRelation()) {
	            System.out.println("ERROR: 'Or' contains numerical expression:"+child);
	            return false;
	        }
	    }
	    return true;
	}
	
	public ASTNode normalise() {
	    normaliseInPlace();
	    return this;
    }
    public ASTNode normaliseAlpha() {
	    normaliseInPlaceAlpha();
	    return null;
    }
    
    public boolean isCommAssoc() {
        return true;
    }
    
    @Override
    public int polarity(int child) {
        return polarity();
    }
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
	{
	    assert bool_context;  // Parent must expect a constraint here. 
	    b.append("watched-or({");
	    for(int i=0; i<numChildren(); i++)
	    {
	        getChild(i).toMinion(b, true);
	        if(i<numChildren()-1) b.append(",");
	    }
	    b.append("})");
	}
	
	public String toString() {
	    StringBuilder b=new StringBuilder();
	    b.append("(");
	    for(int i=0; i<numChildren(); i++) {
	        b.append(getChild(i).toString());
	        if(i<numChildren()-1) b.append(" \\/ ");
	    }
	    b.append(")");
	    return b.toString();
	}
	@Override
	public void toFlatzincWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException {
	    b.append("constraint array_bool_or([");
	    for(int i=0; i<numChildren(); i++) {
            getChild(i).toFlatzinc(b, true);
            if(i<numChildren()-1) b.append(",");
        }
        b.append("],");
        aux.toFlatzinc(b, true);
        b.append(");");
	}
	public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
	    b.append("constraint array_bool_or([");
	    for(int i=0; i<numChildren(); i++) {
            getChild(i).toFlatzinc(b, true);
            if(i<numChildren()-1) b.append(",");
        }
        b.append("],");
        b.append("true);");
	}
	
	public void toMinizinc(StringBuilder b, boolean bool_context) {
	    assert bool_context;
	    b.append("(");
        for(int i=0; i<numChildren(); i++) {
            getChild(i).toMinizinc(b, true);
            if(i<numChildren()-1) b.append(" \\/ ");
        }
        b.append(")");
    }
    
    public void toSAT(Sat satModel) throws IOException {
        ArrayList<Long> clause= new ArrayList<Long>();
        for (int i=0; i<numChildren(); i++) {
            clause.add(getChild(i).directEncode(satModel,1));
        }
        
        satModel.addClause(clause);
    }
    
    public void toSATWithAuxVar(Sat satModel, long auxVar) throws IOException {
        ArrayList<Long> clause=new ArrayList<Long>();
        for (int i=0; i<numChildren(); i++) {
            clause.add(getChild(i).directEncode(satModel,1));
        }
        satModel.addClauseReified(clause, auxVar);
    }
    
    @Override
	public boolean childrenAreSymmetric() {
	    return true;
	}
    public boolean usesSMTEncoding() {
        return true;
    }

    public void toSMT(SMT satModel) throws IOException {
        satModel.addSMTClause(smtEncodeBool(satModel));
    }

    @Override
    public String smtEncodeBool(SMT satModel) {
        String clause = "(or";

        for (int i=0; i<numChildren(); i++)
            clause += " " + getChild(i).smtEncodeBool(satModel);

        return clause + ")";
    }

    @Override
    public String smtEncodeBV(SMT satModel) {
        return "(ite " + this.smtEncodeBool(satModel) + " " + SMT.toSMTBV(1) + " " + SMT.toSMTBV(0) + ")";
    }

    @Override
    public String smtEncodeInt(SMT satModel) {
        return "(ite " + smtEncodeBool(satModel) + " 1 0)";
    }
}
