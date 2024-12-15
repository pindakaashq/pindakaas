package savilerow.solver;
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
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

import savilerow.CmdFlags;

// Stores and outputs to file statistics about solver runs, Savile Row time and configuration.

// Standard names of fields:

// SolverSolveTime
// SolverSetupTime
// SolverTotalTime
// SolverNodes
// SavileRowTotalTime
// SolverSatisfiable
// SolverSolutionsFound
// SolverTimeOut
// SolverMemOut
// SavileRowTimeOut
// SavileRowClauseOut
// SATVars
// SATClauses

// Subclasses are responsible for filling in the fields above (at least).

public class Stats
{
    private HashMap<String, String> values;
    protected HashSet<String> toAdd;
    
    public Stats() {
        values=new HashMap<String, String>();
        String[] toAddArr={"SolverSolveTime", "SolverSetupTime", "SolverTotalTime", "SolverNodes", "SolverSolutionsFound"};
        toAdd = new HashSet<String>(Arrays.asList(toAddArr));   //  stats that are added rather than maxed.
        
        // Default values -- to be overwritten when timeout or clauseout occurs. 
        putValue("SavileRowTimeOut", "0");
        putValue("SavileRowClauseOut", "0");
        
        if(CmdFlags.tabtime>-1.0) {
            putValue("TabulationTime", String.valueOf(CmdFlags.tabtime));
        }
    }
    
    public String getValue(String header) {
        if(values.containsKey(header)) {
            return values.get(header);
        }
        else {
            return "NA";
        }
    }
    
    public void putValue(String header, String value) {
        values.put(header, value);
    }
    
    public boolean hasValue(String header) {
        return values.containsKey(header);
    }
    
    public String toString() {
        // Print key, value pairs. Assumes just one value for each key.
        String st="";
        for(String key : values.keySet()) {
            st+=key+":"+getValue(key)+"\n";
        }
        return st;
    }
    
    // Report to go in solution file. 
    public String report(String header) {
        return "Minion "+header+": "+getValue(header);
    }
    
    //  Write the data in an R friendly format.  Space separated values.   
    public void writeR(BufferedWriter b) throws IOException {
        b.write("\""+ CmdFlags.eprimefile+"\"  ");
        b.write("\""+CmdFlags.paramfile+"\"  ");
        if(CmdFlags.getUsePropagate()) {
            b.write("1  ");
        }
        else {
            b.write("0  ");
        }
        
        if(CmdFlags.getUseACCSE()) {
            b.write("1  ");
        }
        else {
            b.write("0  ");
        }
        
        b.write(CmdFlags.accse_heuristic+"  ");
        
        b.write(getValue("SolverSolveTime")+"  ");
        
        b.write(getValue("SolverTotalTime")+"  ");
        
        b.write(getValue("SolverSetupTime")+"  ");
        
        b.write(getValue("SolverNodes")+"  ");
        
        b.write(getValue("SolverTimeOut")+"  ");
        
        b.write(getValue("SolverSatisfiable")+"  ");
        
        b.write(getValue("SavileRowTotalTime")+"  ");
        
        // New entries since AC-CSE exps
        b.write(getValue("SolverMemOut")+"  ");
        
        b.write(getValue("SavileRowTimeOut")+"  ");
        
        b.write(getValue("SavileRowClauseOut")+"  ");
        
        b.write(getValue("SATVars")+"  ");
        
        b.write(getValue("SATClauses")+"\n");
        
        // Have dropped SolverSolutionsFound!
    }
    
    public Stats add(Stats other) {
        //  Add together this and the other Stats object to make a third.
        Stats tmp = null;
        // if the other stats is interacitve, we need to take care how we report in the future.
        if (other instanceof InteractiveStats) {
            tmp = new InteractiveStats();
        }
        else {
            tmp = new Stats();
        }
        for(String key : values.keySet()) {
            if(toAdd.contains(key)) {
                tmp.putValue(key, sum(other.getValue(key), this.getValue(key)));
            }
            else {
                tmp.putValue(key, max(other.getValue(key), this.getValue(key)));
            }
        }
        
        return tmp;
    }
    
    String max(String a, String b) {
        if (a.equals("NA") && b.equals("NA"))
            return "NA";
        else if (a.equals("NA"))
            return b;
        else if (b.equals("NA"))
            return a;

        if(Double.valueOf(a)>Double.valueOf(b)) {
            return a;
        }
        else {
            return b;
        }
    }
    
    String sum(String a, String b) {
        if (a.equals("NA") && b.equals("NA"))
            return "NA";
        else if (a.equals("NA"))
            return b;
        else if (b.equals("NA"))
            return a;

        return String.valueOf(Double.valueOf(a)+Double.valueOf(b));
    }
    
    public void makeInfoFiles() {
        try {
            BufferedWriter out;
            out= new BufferedWriter(new FileWriter(CmdFlags.infofile, CmdFlags.dominanceRelation));
            
            out.write(this.toString());
            if(CmdFlags.dominanceRelation) out.write("----------\n");
            out.close();
            
            out= new BufferedWriter(new FileWriter(CmdFlags.infofile+"r"));
            this.writeR(out);
            out.close();
            
            CmdFlags.println("Created information file " + CmdFlags.infofile);
        }
        catch (IOException e) {
            CmdFlags.println("Could not open file for info output.");
        }
    }
}
