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

import savilerow.solver.Stats;

// Simple class with main method to read and translate Essence'.

public final class EPrimeTailor {

  /* ====================================================================
     main
    ==================================================================== */ 
    public static void main(String[] args) {
        // Parse the command-line arguments
        CmdFlags.parseArguments(args);
        
        Thread.setDefaultUncaughtExceptionHandler(new Thread.UncaughtExceptionHandler() {
            @Override
            public void uncaughtException(Thread t, Throwable e) {


                if(e instanceof java.lang.OutOfMemoryError) {
                    Stats stats=new Stats();
                    stats.putValue("SavileRowTotalTime", String.valueOf(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000));
                    stats.putValue("SavileRowUncaughtException", "1");
                    stats.putValue("SavileRowOutOfMemory", "1");
                    stats.makeInfoFiles();
                    CmdFlags.errorExit("Out of Memory");
                }
                else {
                    Stats stats=new Stats();
                    stats.putValue("SavileRowTotalTime", String.valueOf(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000));
                    stats.putValue("SavileRowUncaughtException", "1");
                    stats.makeInfoFiles();
                    e.printStackTrace(System.err);
                    CmdFlags.errorExit("Savile Row killed by: " + e.toString());
                }
            }
        });

        SRWorkThread t=new SRWorkThread();
        
        t.start();
        
        if(CmdFlags.getTimeLimit()>0) {
            //   Loop until enough time has passed relative to CmdFlags.startTime
            //   CmdFlags.startTime can be reset by the other thread, in particular following each dry run.  Therefore SR can in total take much longer than the time limit when dry runs are switched on. 
            //   Does not check whether a  dry run is happening, therefore SR /can/ time out if one of the dry runs takes longer than the time limit.  
            while( (System.currentTimeMillis()-CmdFlags.startTime) < CmdFlags.getTimeLimit()) {
                try {
                    long sleepTime=CmdFlags.getTimeLimit()- (System.currentTimeMillis()-CmdFlags.startTime); // sleep for the specified number of milliseconds minus elapsed time so far.
                    if(sleepTime>0L) {
                        Thread.sleep(sleepTime);
                    }
                }
                catch(InterruptedException e1) {
                }
            }
            
            if(!CmdFlags.runningSolver) {
                // If we have not reached the point where the solver is running (to search, not just filter domains)
                // then exit. 
                
                // Create .info and .infor files.
                Stats stats=new Stats();
                stats.putValue("SavileRowTotalTime", String.valueOf(((double) System.currentTimeMillis() - CmdFlags.startTime) / 1000));
                stats.putValue("SavileRowTimeOut", "1");
                stats.makeInfoFiles();
                
                CmdFlags.errorExit("Savile Row timed out.");
            }
        }
    }
}

