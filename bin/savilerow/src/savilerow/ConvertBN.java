package savilerow;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
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

//  Standalone program to convert local score files for Bayesian network
//  inference into Essence Prime.

public class ConvertBN {
    public static void main(String[] args) {
        
        // List of lists of local scores with parent sets. 
        ArrayList<ArrayList<Pair<Double, ArrayList<Integer>>>> inst=new ArrayList<>();
        
        try {
            BufferedReader in=new BufferedReader(new FileReader(args[0]));
            
            // Parse local score file. 
            String line=in.readLine();
            
            // First line must contain a single integer -- the number of variables.
            int numvariables=Integer.parseInt(line);
            
            // Next, lines are grouped for each variable.
            for(int i=0; i<numvariables; i++) {
                line=in.readLine();
                String[] parts=line.split(" ");
                
                int varnumber=Integer.parseInt(parts[0]);
                int numsets=Integer.parseInt(parts[1]);
                
                assert varnumber==i;
                
                ArrayList<Pair<Double, ArrayList<Integer>>> var=new ArrayList<>();
                
                for(int j=0; j<numsets; j++) {
                    line=in.readLine();
                    parts=line.split(" ");
                    
                    double score=Double.parseDouble(parts[0]);
                    
                    ArrayList<Integer> parents=new ArrayList<>();
                    int numparents=Integer.parseInt(parts[1]);
                    for(int k=0; k<numparents; k++) {
                        parents.add(Integer.parseInt(parts[k+2])+1);  //  Change from 0- to 1-based
                    }
                    
                    var.add(new Pair<Double, ArrayList<Integer>>(score, parents));
                }
                
                inst.add(var);
            }
        }
        catch (IOException e) {
            System.err.println(e);
            System.exit(5);
        }
        
        boolean emptySetRemoved=false;
        
        if(emptySetRemoved) {
            // Remove empty parent sets
            double adjust=0.0;
            
            for(int i=0; i<inst.size(); i++) {
                double minscore=Double.MAX_VALUE;
                ArrayList<Pair<Double, ArrayList<Integer>>> par = inst.get(i);
                
                for(int j=0; j<par.size(); j++) {
                    if(par.get(j).getSecond().size()==0) {
                        assert minscore==Double.MAX_VALUE;
                        minscore=par.get(j).getFirst();
                    }
                }
                for(int j=par.size()-1; j>=0; j--) {
                    if(par.get(j).getSecond().size()==0) {
                        par.remove(j);
                    }
                    else {
                        assert par.get(j).getFirst() > minscore;
                        par.get(j).setFirst(par.get(j).getFirst()-minscore);   //  Shift scores relative to empty parentset.
                    }
                }
                adjust+=minscore;
            }
            
            System.out.println("$  Adjustment to objective: "+Math.round(adjust*100));
        }
        
        // Dump to Essence Prime param file.
        
        System.out.println("language ESSENCE' 1.0");
        
        System.out.println("letting nodes="+inst.size());
        
        System.out.println("letting emptySetRemoved="+emptySetRemoved);
        
        ArrayList<ArrayList<String>> varnames=new ArrayList<>();
        
        ArrayList<String> constraints=new ArrayList<String>();
        
        ArrayList<String> opt=new ArrayList<String>();
        
        //  For each node, dump a list of parent sets.
        System.out.println("letting parentSets=[");
        
        for(int i=0; i<inst.size(); i++) {
            ArrayList<Pair<Double, ArrayList<Integer>>> par = inst.get(i);
            
            //  Open bracket for the node. 
            System.out.println("[");
            
            for(int j=0; j<par.size(); j++) {
                //  One parent set. 
                System.out.print(par.get(j).getSecond());
                if(j<par.size()-1) {
                    System.out.print(", ");
                }
                else {
                    System.out.println();
                }
            }
            
            //  Close the node
            if(i<inst.size()-1) {
                System.out.println("],");
            }
            else {
                System.out.println("]");
            }
        }
        
        // Close parentSets
        System.out.println("]");
        
        //  For each node and each parent set, print out the score. 
        System.out.println("letting scores=[");
        
        for(int i=0; i<inst.size(); i++) {
            ArrayList<Pair<Double, ArrayList<Integer>>> par = inst.get(i);
            
            //  Open bracket for the node. 
            System.out.println("[");
            
            for(int j=0; j<par.size(); j++) {
                //  One parent set. 
                System.out.print(Math.round(par.get(j).getFirst()*100));
                if(j<par.size()-1) {
                    System.out.print(", ");
                }
            }
            
            //  Close the node
            if(i<inst.size()-1) {
                System.out.println("],");
            }
            else {
                System.out.println("]");
            }
        }
        
        // Close scores
        System.out.println("]");
        
    }
}
