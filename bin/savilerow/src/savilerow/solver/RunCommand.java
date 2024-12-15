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
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;

import savilerow.CmdFlags;

public class RunCommand
{
    // Returns exit code. 
    public static int runCommand(boolean zeroExitCode, ArrayList<String> command, ArrayList<String> stderr_lines, ReadProcessOutput output_processor) throws IOException,  InterruptedException
    {
        try {

            CmdFlags.printlnIfVerbose("Running command: " + command);

            Process process=Runtime.getRuntime().exec(command.toArray(new String[command.size()]));
            
            InputStream inputStream = process.getInputStream();
            InputStream errorStream = process.getErrorStream();
            BufferedReader input =new BufferedReader(new InputStreamReader(inputStream));
            BufferedReader error =new BufferedReader(new InputStreamReader(errorStream));
            
            ReadProcessOutput rpo2=new ReadProcessOutput(stderr_lines);
            
            output_processor.giveInputStream(input);
            rpo2.giveInputStream(error);
            
            output_processor.start();
            rpo2.start();
            
            output_processor.join();
            rpo2.join();
            
            int exitValue=process.waitFor();
            
            // Some solvers (for example chuffed) print warning messages with WARNING as prefix.
            // We don't want to report sub-process failure if these are the only messages in stderr.
            // So we check whether stderr_lines_except_warnings is empty or not when deciding below.
            ArrayList<String> stderr_lines_except_warnings = new ArrayList<String>();
            for (String line : stderr_lines) {
                line = line.trim();
                // Skip if it's an empty line
                if (line.equals("")) continue;
                // Skip if it start with the word WARNING or Warning
                if (line.toLowerCase().startsWith("warning")) continue;
                stderr_lines_except_warnings.add(line);
            }
            
            if(zeroExitCode && (stderr_lines_except_warnings.size()!=0 || (exitValue!=0 && exitValue!=10 && exitValue!=20))) {
                // Exit values 10 and 20 typical for SAT solvers to indicate sat or unsat. 
                CmdFlags.println("Sub-process exited with error code:"+exitValue+" and error message:");
                CmdFlags.println(stderr_lines);
            }
            return exitValue;
        }
        catch(IOException e1) {
            System.err.println("IOException");
            e1.printStackTrace();
            throw e1;
        }
        catch(InterruptedException e2) {
            System.out.println("InterruptedException.");
            throw e2;
        }
    }
}
