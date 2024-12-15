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


public class PairASTNode
{
    public ASTNode e1;
    public ASTNode e2;
    public PairASTNode(ASTNode a1, ASTNode a2) {e1=a1; e2=a2;}
    
    @Override
    public int hashCode() {
        int hash=this.getClass().hashCode();
        hash=hash*13+e1.hashCode();
        hash=hash*17+e2.hashCode();
        return hash;
    }
    
    @Override
	public boolean equals(Object b)
	{
	    if(!(b instanceof PairASTNode))
	        return false;
	    PairASTNode temp=(PairASTNode) b;
	    return e1.equals(temp.e1) && e2.equals(temp.e2);
	}
	
    public String toString() {
        return "("+e1+" , "+e2+")";
    }
}
