package savilerow.mdd;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Jordi Coll
    
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

import savilerow.Pair;

//  Class checked against Jordi's code 17/3/2021
public class MDD
{
    public static final long serialVersionUID = 1L;
    
    //  id > id of any child (not just direct child)
    int id;
    
    ArrayList<Long> selectors;   //  Literals
    ArrayList<MDD> children;
    MDD elsechild;
    
    boolean istrivialtrue;
    boolean istrivialfalse;
    
    //  Number of variables in the Boolean function that this MDD represents, plus 1
	//  It is equivalent to the depth of an OMDD without any long edge (i.e. all variables appear in the MDD)
    int vardepth;
    
    // Number of layers with some node in the MDD. Notice that realdepth<=vardepth
	int realdepth;
    
    static MDD mddtrue;    // true and false leaf nodes. 
    static MDD mddfalse;
    
    //  Trivial constructor for true or false leaf nodes.
    private MDD(boolean b) {
        id=b ? 1 : 0;
        istrivialtrue = b;
        istrivialfalse = !b;
        vardepth = 1;
        realdepth = 1;
        selectors=new ArrayList<Long>();
        children=new ArrayList<MDD>();
    }
    
    //  Constructor for non-leaf nodes.
    public MDD(int _id, int nvars) {
        id = _id;
        istrivialtrue=false;
        istrivialfalse=false;
        vardepth=nvars+1;
        realdepth = 0;
        selectors=new ArrayList<Long>();
        children=new ArrayList<MDD>();
    }
    
    public static MDD MDDFalse() {
        if(mddfalse==null) {
            mddfalse = new MDD(false);
        }
        return mddfalse;
    }
    
    public static MDD MDDTrue() {
        if(mddtrue==null) {
            mddtrue = new MDD(true);
        }
        return mddtrue;
    }
    
    public ArrayList<Long> getSelectors() {
        return selectors;
    }
    
    public MDD getChildByIdx(int idx) {
        return children.get(idx);
    }
    
    public MDD getChild(long selector) {
        for(int i = 0; i < selectors.size(); i++) {
            if(selectors.get(i)==selector) {
                return children.get(i);
            }
        }
        return null;
    }
    
    public MDD getElseChild() {
        return elsechild;
    }
    
    public int getId() {
        return id;
    }
    
    public int getVarDepth() {
        return vardepth;
    }
    
    public int getRealDepth() {
        return realdepth;
    }
    
    public int getSize() {
        if(isLeafMDD()) {
            return 1;
        }
        return getSize(new boolean[id+1]);
    }
    
    private int getSize(boolean[] visited) {
        if(!visited[id]){
            visited[id]=true;
            int size=1;
            if(!isLeafMDD()) {
                for(int i=0; i<children.size(); i++) {
                    size+=children.get(i).getSize(visited);
                }
                size+=elsechild.getSize(visited);
            }
            return size;
        }
        return 0;
    }
    
    public int getIdBasedSize() {
        return isLeafMDD() ? 1 : id+1;
    }
    
    /*
    //  Not checked against Jordi's version. 
    public int getLayerWidth() {
        boolean[] visited = new boolean[id+1];
        
        ArrayList<MDD> q=new ArrayList<MDD>();
        ArrayList<ArrayList<MDD>> layers = new ArrayList<ArrayList<MDD>>(getVarDepth());
        for(int i=0; i<getVarDepth(); i++) {
            layers.add(new ArrayList<MDD>());
        }
        
        q.add(this);
        visited[id]=true;
        
        while(!q.isEmpty()){
            MDD m = q.get(0);
            q.remove(0);  //  yikes.
            layers.get(m.getVarDepth()-1).add(m);
            if(!m.isLeafMDD()) {
                for(MDD child : m.children) {
                    if(!visited[child.getId()]) {
                        q.add(child);
                        visited[child.getId()]=true;
                    }
                }
                MDD child = m.elsechild;
                if(!visited[child.getId()]){
                    q.add(child);
                    visited[child.getId()]=true;
                }
            }
        }
        int maxWidth = 0;
        for(int i = 0; i < getVarDepth(); i++){
            if(layers.get(i).size()>maxWidth) {
                maxWidth = layers.get(i).size();
            }
        }
        
        return maxWidth;
    }*/
    
    public int getNBinClauses() {
        return isLeafMDD() ? 0 : getSize()-2;
    }
    
    /*
    //  Not checked against Jordi's version. 
    public int getNTernClauses() {
        if(isLeafMDD()) {
            return 0;
        }
        
        int nclauses = 0;
        
        boolean[] visited = new boolean[id+1];
        
        ArrayList<MDD> q=new ArrayList<MDD>();
        q.add(this);
        visited[getId()]=true;
        
        while(!q.isEmpty()) {
            MDD m = q.get(0);
            q.remove(0);   //  yikes
            if(!m.isLeafMDD()) {
                for(MDD child : m.children) {
                    if(child != m.elsechild) {
                        nclauses++;
                    }
                    if(!visited[child.getId()]) {
                        q.add(child);
                        visited[child.getId()]=true;
                    }
                }
                MDD child = m.elsechild;
                if(!visited[child.getId()]){
                    q.add(child);
                    visited[child.getId()]=true;
                }
            }
        }
        
        return nclauses;
    }*/
    
    public int getNSelectors() {
        return selectors.size();
    }
    
    public boolean isLeafMDD() {
        return istrivialtrue || istrivialfalse;
    }
    
    public boolean isTrueMDD() {
        return istrivialtrue;
    }
    
    public boolean isFalseMDD() {
        return istrivialfalse;
    }
    
    public Pair<Long, MDD> getSelectorAndChild(int idx) {
        return new Pair<Long,MDD>(selectors.get(idx),children.get(idx));
    }
    
    public void addChild(long selector, MDD child){
        children.add(child);
        selectors.add(selector);
        if(child.realdepth >= this.realdepth) {
            this.realdepth = child.realdepth+1;
        }
    }
    
    public void setElseChild(MDD child){
        elsechild = child;
        if(child.realdepth >= this.realdepth) {
            this.realdepth = child.realdepth+1;
        }
    }
}
