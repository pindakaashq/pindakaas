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


// Thing to allow methods to return two objects. 

public class Pair<A,B> {
    private A first;
    private B second;
    public Pair(A first, B second) {
        this.first = first;
        this.second = second;
    }
    
    public A getFirst() {return first;}
    public B getSecond() {return second;}
    public void setFirst(A f) {first=f;}
    public void setSecond(B s) {second=s;}
    
    @Override public int hashCode() {
        return (1013 * (first.hashCode())) ^ (1009 * (second.hashCode()));
    }
    
    @Override public boolean equals(Object other) {
    	if (other instanceof Pair) {
    	    return ((Pair)other).getFirst().equals(first) && ((Pair)other).getSecond().equals(second);
    	}
    	return false;
    }
    
    public String toString() {
        return "("+first.toString()+","+second.toString()+")";
    }
}

