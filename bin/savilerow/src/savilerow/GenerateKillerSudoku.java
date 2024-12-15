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
import java.util.Collections;
import java.util.Random;

import savilerow.eprimeparser.EPrimeReader;
import savilerow.expression.*;
import savilerow.model.*;

// Simple class with main method to read and translate Essence'.

public final class GenerateKillerSudoku {

  /* ====================================================================
     main for testing
    ==================================================================== */ 
    public static void main(String[] args) {
        // Parse the command-line arguments
        
        String solfile=args[0];
        
        // read the solution
        EPrimeReader reader = new EPrimeReader(solfile, true);
        
        Model m=new Model();
        m.setup(new BooleanConstant(true), new SymbolTable(), null, null, null, null, null);
        
        ArrayList<ASTNode> sol=reader.readParameterFile(m);
        
        ASTNode solmatrix=sol.get(0).getChild(1); // unpick the letting. 
        
        //System.out.println("Solution:" + solmatrix);
        
        // A clue is a length 2-5 shape that is contiguous 
        // 
        
        ArrayList<ArrayList<Boolean>> taken=new ArrayList<ArrayList<Boolean>>();
        for(int i=0; i<16; i++) {
            ArrayList<Boolean> tmp=new ArrayList<Boolean>(Collections.nCopies(16, false));
            taken.add(tmp);
        }
        
        ArrayList<ArrayList<Integer>> clues=new ArrayList<ArrayList<Integer>>();
        
        // Mkae clues starting from random places. 
        Random rand = new Random();
        int count_fails=0;
        while(count_fails<10) {
            int x=rand.nextInt(16);
            int y=rand.nextInt(16);
            if(taken.get(x).get(y)) {
                count_fails++;
            }
            else {
                count_fails=0;
                ArrayList<Integer> clue=makeClue(x,y,taken);
                
                boolean containsRepeat=false;
                
                jloop:
                for(int j=0; j<clue.size(); j=j+2) {
                    for(int k=j+2; k<clue.size(); k=k+2) {
                        if( solmatrix.getChild(clue.get(j)+1).getChild(clue.get(j+1)+1).getValue() 
                            == solmatrix.getChild(clue.get(k)+1).getChild(clue.get(k+1)+1).getValue()) {
                            containsRepeat=true;
                            break jloop;
                        }
                    }
                }
                
                if(!containsRepeat) {
                    clues.add(clue);
                }
            }
        }
        
        
        
        // fill in clues from top left
        for(int i=0; i<taken.size(); i++) {
            for(int j=0; j<taken.get(i).size(); j++) {
                if(!taken.get(i).get(j)) {
                    
                    whiletrue:
                    while(true) {
                        ArrayList<Integer> clue=makeClue(i,j,taken);
                    
                        boolean containsRepeat=false;
                        
                        jloop:
                        for(int l=0; l<clue.size(); l=l+2) {
                            for(int k=l+2; k<clue.size(); k=k+2) {
                                if( solmatrix.getChild(clue.get(l)+1).getChild(clue.get(l+1)+1).getValue() 
                                    == solmatrix.getChild(clue.get(k)+1).getChild(clue.get(k+1)+1).getValue()) {
                                    containsRepeat=true;
                                    break jloop;
                                }
                            }
                        }
                        
                        if(!containsRepeat) {
                            clues.add(clue);
                            break whiletrue;
                        }
                    }
                }
            }
        }
        
        //System.out.println("Clues:"+clues);
        //System.out.println("Taken:"+taken);
        
        // dump param file. 
        
        System.out.println("language ESSENCE' 1.0");
        
        System.out.println("letting lastdx="+(clues.size()-1));
        
        System.out.println("letting cage be [");
        
        for(int i=0; i<clues.size(); i++) {
            long sum=0;
            ArrayList<Integer> clue=clues.get(i);
            for(int j=0; j<clue.size(); j=j+2) {
                ASTNode value=solmatrix.getChild(clue.get(j)+1).getChild(clue.get(j+1)+1);
                sum=sum+value.getValue();
            }
            
            System.out.print("["+sum+",");
            
            
            for(int j=0; j<clue.size(); j=j+2) {
                System.out.print(clue.get(j)+1);
                System.out.print(",");
                System.out.print(clue.get(j+1)+1);
                if(j<8) System.out.print(",");
            }
            
            for(int j=clue.size(); j<=8; j=j+2) {
                System.out.print("0,0");
                if(j<8) System.out.print(", ");
            }
            
            System.out.print("]");
            if(i<clues.size()-1) System.out.print(",");
            System.out.println();
        }
        
        System.out.println("]");
    }
    
    public static ArrayList<Integer> makeClue(int x, int y, ArrayList<ArrayList<Boolean>> taken) {
        // Build up a clue starting at x and y,
        ArrayList<Integer> clue=new ArrayList<Integer>();
        clue.add(x); clue.add(y);
        
        assert !taken.get(x).get(y);
        taken.get(x).set(y, true);
        
        // Add newly blocked-off squares. 
        ArrayList<Integer> tmp=squareBlockedOff(taken);
        
        for(int i=0; i<tmp.size(); i=i+2) {
            taken.get(tmp.get(i)).set(tmp.get(i+1), true);
            clue.add(tmp.get(i));
            clue.add(tmp.get(i+1));
        }
        
        Random rand = new Random();
        
        int cluesize= rand.nextInt(5) + 1;   // Allow size 1 clues
        
        int r=rand.nextInt(100);
        
        if(r<40) {
            cluesize=1;
        }
        else if(r<55) {
            cluesize=2;
        }
        else if(r<70) {
            cluesize=3;
        }
        else if(r<85) {
            cluesize=4;
        }
        else {
            cluesize=5;
        }
        
        
        
        while(clue.size()/2 < cluesize) {
            
            if( validNeighbour(x-1,y, taken, clue.size()/2) || validNeighbour(x+1, y, taken, clue.size()/2) 
                || validNeighbour(x, y-1, taken, clue.size()/2) || validNeighbour(x, y+1, taken, clue.size()/2)) {
                // Can be extended. 
                
                int newx, newy;
                
                while(true) {
                    int neighbour=rand.nextInt(4);
                    if(neighbour==0 && validNeighbour(x-1, y, taken, clue.size()/2)) {
                        // make the move. 
                        newx=x-1;
                        newy=y;
                        break;
                    }
                    if(neighbour==1 && validNeighbour(x+1, y, taken, clue.size()/2)) {
                        // make the move. 
                        newx=x+1;
                        newy=y;
                        break;
                    }
                    if(neighbour==2 && validNeighbour(x, y-1, taken, clue.size()/2)) {
                        // make the move. 
                        newx=x;
                        newy=y-1;
                        break;
                    }
                    if(neighbour==3 && validNeighbour(x, y+1, taken, clue.size()/2)) {
                        // make the move. 
                        newx=x;
                        newy=y+1;
                        break;
                    }
                }
                
                clue.add(newx);
                clue.add(newy);
                taken.get(newx).set(newy, true);
                
                // Add newly blocked-off squares. 
                tmp=squareBlockedOff(taken);
                
                for(int i=0; i<tmp.size(); i=i+2) {
                    taken.get(tmp.get(i)).set(tmp.get(i+1), true);
                    clue.add(tmp.get(i));
                    clue.add(tmp.get(i+1));
                }
                
                x=newx;
                y=newy;
            }
            else {
                break;
            }
        }
        
        return clue;
    }
    
    public static boolean validNeighbour(int x, int y, ArrayList<ArrayList<Boolean>> taken, int cluesize_so_far) {
        if(x<0 || x>=16) return false;
        if(y<0 || y>=16) return false;
        
        if(taken.get(x).get(y)) return false;
        
        // If it blocks off a single square
        taken.get(x).set(y, true);   // temporarily
        ArrayList<Integer> tmp=squareBlockedOff(taken);
        
        taken.get(x).set(y, false);
        
        // If this move were taken, it would entail adding tmp.size()/2 other squares as well. If it goes over five, reject it. 
        if((tmp.size()/2)+cluesize_so_far+1>5) return false; 
        
        return true;
    }
    
    public static ArrayList<Integer> squareBlockedOff(ArrayList<ArrayList<Boolean>> taken) {
        ArrayList<Integer> blocked_off_squares=new ArrayList<Integer>();
        
        for(int i=0; i<taken.size(); i++) {
            for(int j=0; j<taken.get(i).size(); j++) {
                if( (!taken.get(i).get(j))  &&
                    ( i-1<0 || taken.get(i-1).get(j) ) &&
                    (i+1>=16 || taken.get(i+1).get(j) ) &&
                    (j-1<0  || taken.get(i).get(j-1) ) &&
                    (j+1>=16 || taken.get(i).get(j+1) ))
                {
                    blocked_off_squares.add(i);
                    blocked_off_squares.add(j);
                }
            }
        }
        
        return blocked_off_squares;
    }
    
}
