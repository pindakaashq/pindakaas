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

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

import savilerow.eprimeparser.EPrimeReader;
import savilerow.expression.*;
import savilerow.model.*;
import savilerow.treetransformer.*;
import savilerow.solver.MinionSolver;

// This thread does all the work. The main thread sleeps until timeout, then
// wakes and kills this thread. 

public final class SRWorkThread extends Thread {
    public void run() {
        if(CmdFlags.getMode()==CmdFlags.ReadSolution || CmdFlags.getMode()==CmdFlags.ReadDomainStore) {
            MinionSolver min=new MinionSolver();
            if(CmdFlags.getMode()==CmdFlags.ReadSolution) {
                min.parseSolutionMode();
            }
            else {
                min.parseDomainStore();
            }
            System.exit(0);
        }
        
        //  Read the files.
        Model m;
        if(!CmdFlags.param_to_json) {
            EPrimeReader reader = new EPrimeReader(CmdFlags.eprimefile, true);
            m=reader.readModel() ;
            assert m.constraints != null;
        }
        else {
            m=new Model();  // Empty model object.
            m.global_symbols=new SymbolTable();
        }
        
        // Get the parameters
        ArrayList<ASTNode> parameters=new ArrayList<ASTNode>();
        if(CmdFlags.paramfile!=null) {
            EPrimeReader paramfile = new EPrimeReader(CmdFlags.paramfile, true);
            parameters=paramfile.readParameterFile(m);
        }
        if(CmdFlags.paramstring!=null) {
            EPrimeReader paramfile = new EPrimeReader(CmdFlags.paramstring, false);
            parameters=paramfile.readParameterFile(m);
        }
        
        ModelContainer mc=new ModelContainer(m, new ArrayList<ASTNode>(parameters));
        
        if(CmdFlags.param_to_json) {
            paramToJSON(parameters, m);
            System.exit(0);
        }
        
        if(CmdFlags.dryruns) {
            //  Three dry runs.  Reset the clock after each one; if there is a timeout during a dryrun then SR will exit.
            //  For the timelimit, time starts again for each dryrun.
            
            ModelContainer mc2=mc.copy();
            mc2.dryrun();
            CmdFlags.startTime=System.currentTimeMillis();
            
            mc2=mc.copy();
            mc2.dryrun();
            CmdFlags.startTime=System.currentTimeMillis();
            
            mc2=mc.copy();
            mc2.dryrun();
            CmdFlags.startTime=System.currentTimeMillis();
        }
        
        CmdFlags.startTime=System.currentTimeMillis();
        
        if(CmdFlags.make_tab) {
            mc.makeTableScopes();
        }
        else {
            mc.process();
        }
        
        System.exit(0);  // This is needed otherwise the other thread (Main thread) will continue to 
        // sleep and SR will not exit when it has finished. 
    }
    
    // This should really be somewhere else -- dump JSON version of param file.
    public void paramToJSON(ArrayList<ASTNode> parameters, Model m) {
        
        //  Interpret the parameter file. This version dumps any generated 
        for (int i =0; i < parameters.size(); i++) {
            ASTNode a = parameters.get(i);
            
            TransformMakeSafe tms = new TransformMakeSafe(m);
            a = tms.transform(a);
            
            TransformSimplify ts = new TransformSimplify();
            a = ts.transform(a);
            
            // Unroll and evaluate any matrix comprehensions or quantifiers in the parameters.
            TransformQuantifiedExpression t2 = new TransformQuantifiedExpression(m);
            a = t2.transform(a);
            
            a = ts.transform(a);
            
            parameters.set(i, a);
            
            // Scan forward in the parameters to sub this parameter into future ones.
            ReplaceASTNode rep = new ReplaceASTNode(a.getChild(0), a.getChild(1));
            for (int j = i + 1; j < parameters.size(); j++) {
                parameters.set(j, rep.transform(parameters.get(j)));
            }
        }
        
        
        try {
            BufferedWriter o=new BufferedWriter(new FileWriter(CmdFlags.paramfile+".json"));
            
            o.write("{\n");
            for(int i=0; i< parameters.size(); i++) {
                o.write("\"");
                o.write(parameters.get(i).getChild(0).toString());
                o.write("\" : ");
                ASTNode a=parameters.get(i).getChild(1);
                
                TransformSimplify ts=new TransformSimplify();
                a=ts.transform(a);
                
                if(a instanceof BooleanConstant || a instanceof NumberConstant) {
                    o.write(a.toString());
                }
                else if(a instanceof EmptyMatrix) {
                    o.write("[ ]");
                }
                else {
                    o.write(((CompoundMatrix)a).toStringSimpleMatrix());
                }
                if(i<parameters.size()-1) {
                    o.write(",");
                }
                o.write("\n");
            }
            
            o.write("}\n");
            o.close();
        }
        catch(IOException blah) {
        }
    }
}

