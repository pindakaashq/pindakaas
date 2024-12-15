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
import java.util.HashMap;

import savilerow.expression.*;
import savilerow.model.Model;

// For all Elements, if the index expression is an aux variable, get the
// constraint that defines it and make sure that constraint enforces
// GAC. 

public class ElementGAC 
{
    private HashMap<ASTNode, ASTNode> auxs=new HashMap<ASTNode, ASTNode>();
    
    private ArrayList<ASTNode> elements=new ArrayList<ASTNode>();
    
    public void transform(Model m) {
        populate_auxs(m.constraints.getChild(0));
        
        for(int i=0; i<elements.size(); i++) {
            ASTNode e=elements.get(i);
            
            if(e.getChild(1) instanceof Identifier && ((Identifier)e.getChild(1)).isAuxiliary()) {
                ASTNode auxvar=e.getChild(1);
                ASTNode auxct=auxs.get(auxvar);
                
                if(auxct!=null && !(auxct.strongProp())) {
                    //  Replace the weakly propagating constraint with a table.
                    
                    Tabulation t=new Tabulation(m);
                    
                    ASTNode replct=t.tabulate(auxct, Long.MAX_VALUE, (CmdFlags.make_short_tab==2 || CmdFlags.make_short_tab==4), "ElementGAC");
                    
                    auxct.getParent().setChild(auxct.getChildNo(), replct);
                    //System.out.println("Replaced: "+auxct+" with:"+replct);
                    //  Replace in hash table.
                    auxs.put(auxvar, replct);
                }
            }
        }
    }
    
    private void populate_auxs(ASTNode a)  {
        if(a.getParent().inTopAnd() && (a instanceof ToVariable || a instanceof Equals || a instanceof Iff)) {
            if(a.getChild(0) instanceof Identifier && ((Identifier)a.getChild(0)).isAuxiliary()) {
                auxs.put(a.getChild(0), a);
            }
            if(a.getChild(1) instanceof Identifier && ((Identifier) a.getChild(1)).isAuxiliary()) {
                auxs.put(a.getChild(1), a);
            }
        }
        if(a instanceof ElementOne) {
            elements.add(a);
        }
        for(int i=0; i<a.numChildren(); i++) {
            populate_auxs(a.getChild(i));
        }
    }
}


