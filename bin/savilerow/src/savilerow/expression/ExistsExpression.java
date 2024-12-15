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

import savilerow.treetransformer.ReplaceASTNode;

public class ExistsExpression extends Quantifier
{
    public static final long serialVersionUID = 1L;
    public ExistsExpression(ASTNode i, ASTNode d, ASTNode e) {
        super(i,d,e);
    }
    
	public ASTNode copy()
	{
	    return new ExistsExpression(getChild(0), getChild(1), getChild(2));
	}
	public boolean isRelation(){return true;}
	
	public ASTNode simplify() {
	    /*
	    // Is this correct? What if domain is empty?
	    if(! getChild(2).contains(getChild(0))) {
	        // Identifier not used anywhere.
	        return getChild(2);
	    }*/
	    
	    if(getChild(1) instanceof SimpleDomain && getChild(1).getCategory()==ASTNode.Constant) {
	        
	        // If the domain is large, don't unroll.
	        Intpair dombnds=getChild(1).getBounds();
	        if(dombnds.lower+100 >= dombnds.upper) {
	            // Unroll it. This is supposed to be an optimisation to speed up TransformQuantifiedExpression by helping
	            // TQE to simplify while unrolling.
                ArrayList<Intpair> qvals=getChild(1).getIntervalSet();
                ArrayList<ASTNode> expansion=new ArrayList<ASTNode>();
                for(int i=0; i<qvals.size(); i++) {
                    for(long val=qvals.get(i).lower; val<=qvals.get(i).upper; val++) {
                        ASTNode unfoldedExpression=getChild(2).copy();
                        
                        // Sub in the value. 
                        ReplaceASTNode t=new ReplaceASTNode(getChild(0), NumberConstant.make(val));
                        unfoldedExpression=t.transform(unfoldedExpression);
                        
                        expansion.add(unfoldedExpression);
                    }
                }
                
                return new Or(expansion);
            }
	    }
	    
	    // Should check for unit domains here.
	    
	    /*if(getChild(2) instanceof ExistsExpression) {
	        ArrayList<ASTNode> newidlist=getChild(0).getChildren();
	        newidlist.addAll(getChild(2).getChild(0).getChildren());
	        setChild(0, new Container(newidlist));
	        
	        ArrayList<ASTNode> newdomlist=getChild(1).getChildren();
	        newdomlist.addAll(getChild(2).getChild(1).getChildren());
	        setChild(1, new Container(newdomlist));
	        setChild(2, getChild(2).getChild(2));
	    }*/
	    return null;
	}
	
	public String toString() {
	    return "(exists "+getChild(0)+" : "+getChild(1)+" . "+getChild(2)+")";
	}
}
