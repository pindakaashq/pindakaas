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

import java.util.ArrayList;

import gnu.trove.map.hash.TObjectIntHashMap;
import savilerow.expression.*;
import savilerow.model.*;

//  Remove redundant vars:
//  Add constraint assigning any variables that are not mentioned in any existing constraint or the objective function.
//
//  Dead store elimination (todo):
//  Find vars only mentioned once, as a function of some other variables, and
//  replace the function constraint with a constraint assigning the functional variable. 

public class RemoveRedundantVars 
{
    private TObjectIntHashMap<String> varCount;
    
    public void transform(Model m) {
        varCount=new TObjectIntHashMap<String>();
        assert varCount.getNoEntryValue()==0;
        
        populate_varCount(m.constraints);
        
        if(m.objective!=null) {
            populate_varCount(m.objective);
        }
        
        ArrayList<ASTNode> newConstraints=new ArrayList<ASTNode>();
        
        categoryentry x=m.global_symbols.getCategoryFirst();
        
        while(x!=null) {
            if(m.global_symbols.getCategory(x.name)==ASTNode.Decision) {
                // Includes find and auxiliary variables. 
                
                if(varCount.get(x.name)==varCount.getNoEntryValue()) {
                    ASTNode id=new Identifier(m, x.name);
                    if(!m.global_symbols.preserveVariable(id)) {
                        newConstraints.add(new Equals(id, NumberConstant.make(id.getBounds().lower)));
                    }
                }
            }
            x=x.next;
        }
        
        if(newConstraints.size()>0) {
            // Add new constraints to model.
            m.constraints.getChild(0).setParent(null); /// Do not copy all the constraints
            m.constraints=new Top(new And(m.constraints.getChild(0), new And(newConstraints)));
            m.simplify();
        }
    }
    
    private void populate_varCount(ASTNode a)  {
        if(a instanceof Identifier) {
            String aname=a.toString();
            if(varCount.get(aname)==varCount.getNoEntryValue()) {
                varCount.put(aname, 1);
            }
            else {
                varCount.put(aname, varCount.get(aname)+1);
            }
        }
        else {
            for(int i=0; i<a.numChildren(); i++) {
                populate_varCount(a.getChild(i));
            }
        }
    }
}


