package savilerow.expression;
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

// Contains a set of letting statements 

public class Solution extends ASTNodeC
{
    public static final long serialVersionUID = 1L;
    ArrayList<String> comments;
    public long optval;
    
    public Solution(ArrayList<ASTNode> a, ArrayList<String> com) {
		super(a);
		comments=com;
		optval=0;
	}
	public Solution(ArrayList<ASTNode> a, ArrayList<String> com, long _optval) {
	    super(a);
	    comments=com;
	    optval=_optval;
	}
	
	public ASTNode copy() {
	    return new Solution(getChildren(), new ArrayList<String>(comments));
	}
	
	public String toString() {
	    StringBuilder st=new StringBuilder("language ESSENCE' 1.0\n");
	    for(String com : comments) {
	        st.append("$ "); st.append(com); st.append("\n");
	    }
	    for(ASTNode let : getChildren()) {
	        st.append(let); st.append("\n");
	    }
	    return st.toString();
	}
	
    // used for -solutions-to-stdout-one-line
	public String toStringOneLine() {
	    StringBuilder st=new StringBuilder("language ESSENCE' 1.0\n");
	    for(ASTNode let : getChildren()) {
	        st.append(let); st.append(" ");
	    }
	    return st.toString();
	}
	
	public void addComment(String a) {
	    comments.add(a);
	}
}

