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

public abstract class MDDBuilder
{
    public static final long serialVersionUID = 1L;
    
    //Root node of the built MDD
	public MDD root;
	
	//Depth of the MDD
	public int depth;	
	
	//Number of nodes of the built MDD
	public int nodeCount;
	
	public boolean longedges;
	
	public abstract void buildMDD();
	
    //Constructor
	public MDDBuilder() {
	    nodeCount=2;
	    root=null;
	}
	
	public MDD getMDD() {
	    if(root == null) {
	        buildMDD();
	    }
	    return root;
	}
	
	public int getSize() {
	    return nodeCount == 2 ? 1 : nodeCount;
	}
}
