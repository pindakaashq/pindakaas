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

import java.io.BufferedReader;
import java.io.IOException;
import java.util.ArrayList;

import savilerow.CmdFlags;

public class ReadProcessOutput extends Thread {
    ReadProcessOutput() {}
    
    public ReadProcessOutput(ArrayList<String> _out) {
        out=_out;
    }
    
    BufferedReader br;
    ArrayList<String>   out;
    
    public void giveInputStream(BufferedReader _br) {
        br=_br;
    }
    
    public void run() {
        try {
            String line=br.readLine();
            
            if(CmdFlags.recordObjectiveValues()) {
                while(line != null) {
                    
                    // recording intermediate objective values in file
                    String prefix = "Solution found with Value: ";
                    //System.out.println(line);
                    if (line.startsWith(prefix)) {
                        long value = Long.parseLong(line.substring(prefix.length()));
                        CmdFlags.recordIntermediateObjectiveValue(value);
                    }
                    
                    out.add(line);
                    line=br.readLine();
                }
            }
            else {
                // A simpler loop
                while(line != null) {
                    out.add(line);
                    line=br.readLine();
                }
            }
        }
        catch(IOException e1) {
            CmdFlags.errorExit("IO Exception when reading stdout/stderr from sub-process.");
        }
    }
}
