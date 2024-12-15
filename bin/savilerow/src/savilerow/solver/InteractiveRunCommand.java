package savilerow.solver;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Gökberk Koçak
    
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
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.util.ArrayList;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicInteger;

import savilerow.CmdFlags;
import savilerow.model.*;

public class InteractiveRunCommand {

    Model model;

    Process process;
    // This input stream will be read by a thread and will be processed by main
    // thread after sat/unsat.
    BufferedReader input;
    // This output stream will be fed with model instead of the file i/o.
    public BufferedWriter output;

    ConcurrentLinkedQueue<String> outputContents;

    public ArrayList<String> stdout_lines;

    CountDownLatch isSolverDone;

    AtomicInteger solverResult; // 0 unset, 1 sat, 2 unsat, 3 unknown

    String smtLastVar;

    public InteractiveRunCommand(Model m, ArrayList<String> command) {
        try {
            model = m;
            ProcessBuilder builder = new ProcessBuilder(command);
            builder.redirectErrorStream(true);
            process = builder.start();
            input = new BufferedReader(new InputStreamReader(process.getInputStream()));
            output = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
            isSolverDone = new CountDownLatch(1);
            solverResult = new AtomicInteger(0);
            outputContents = new ConcurrentLinkedQueue<String>();
            stdout_lines = new ArrayList<String>();
            startOutputHandlerThread();
        } catch (IOException e) {
            CmdFlags.errorExit("IRC failure");
            e.printStackTrace();
        }

    }

    private void startOutputHandlerThread() throws IOException {
        Thread readerThread = new Thread(new Runnable() {
            @Override
            public void run() {
                while (true) {
                    try {
                        String line = input.readLine();
                        if ("sat".equals(line) || "unsat".equals(line) || "unknown".equals(line) || line.contains(smtLastVar)) {
                            if ("sat".equals(line.trim())) {
                                solverResult.set(1);
                            } else if ("unsat".equals(line.trim())) {
                                solverResult.set(2);
                            } else {
                                solverResult.set(3);
                            }
                            isSolverDone.countDown();
                        }
                        outputContents.add(line);
                    } catch (IOException e) {
                        CmdFlags.errorExit("IRC BR failure");
                        e.printStackTrace();
                    }

                }
            }
        });
        readerThread.start();
    }

    private String getCheckCommand(){
        if (((InteractiveSMT)model.satModel).activeAssumptions.size() > 0){
            StringBuilder sb = new StringBuilder();
            sb.append("(check-sat-assuming (");
            for(String assumption : ((InteractiveSMT)model.satModel).activeAssumptions){
                sb.append(assumption);
                sb.append(" ");
            }
            sb.setLength(sb.length() - 1);
            sb.append("))");
            return sb.toString();
        }
        else {
            return "(check-sat)";
        }
    }

    /**
     * Returns 10 SAT, 20 UNSAT, 30 UNKNOWN
     */
    public int processCurrentModel(){

        // Start with setting smt last Var for reading purposes
        smtLastVar = ((InteractiveSMT)model.satModel).getLastVarPrefix();
        try {
            output.write(getCheckCommand());
            output.newLine();
            output.flush();
        } catch (IOException e) {
            CmdFlags.errorExit("Output stream failure");
        }

        // wait reader to read stuff (sat/unsat/unknown)
        try {
            isSolverDone.await();
        } catch (InterruptedException e) {
            CmdFlags.errorExit("Thread interrupred");
        }

        int exitValue = solverResult.get();

        // clean the steam
        outputContents.clear();

        // if there is a model to read, request it and wait for it.
        try {
            if (exitValue == 1){
                //set read latch first
                isSolverDone = new CountDownLatch(1);
                ((InteractiveSMT)model.satModel).requestVariableStream();
                isSolverDone.await();
            }
        } catch (IOException e) {
            CmdFlags.errorExit("Output stream failure");
        } catch (InterruptedException e) {
            CmdFlags.errorExit("Thread interrupred");
        }


        // transfer into stdout_lines
        stdout_lines.clear();
        while (outputContents.size() > 0) {
            String polledLine = outputContents.poll();
            // maybe clean errors here
            if (!polledLine.contains("(error")){
                stdout_lines.add(polledLine);
            }
        }

        // set latch for next run, set solver state to fresh
        isSolverDone = new CountDownLatch(1);
        solverResult.set(0);

        if (exitValue == 0) {
            CmdFlags.errorExit("Solver state is unset. Probably a bug");
        }

        return exitValue * 10;

    }
}
