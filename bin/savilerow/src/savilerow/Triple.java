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


// Thing to allow methods to return three objects. 

public class Triple<A,B,C> {
    private A first;
    private B second;
    private C third;
    public Triple(A first, B second, C third) {
        this.first = first;
        this.second = second;
        this.third=third;
    }
    
    public A getFirst() {return first;}
    public B getSecond() {return second;}
    public C getThird() {return third;}
    
    public int hashCode() {
        //  Multiply by prime numbers and xor together. 
        return (1609 * first.hashCode()) ^ (2339 * second.hashCode()) ^ (2707 * third.hashCode());
    }
    
    public boolean equals(Object other) {
    	if (other instanceof Triple) {
    	    return ((Triple)other).getFirst().equals(first) && ((Triple)other).getSecond().equals(second) && ((Triple)other).getThird().equals(third);
    	}
    	return false;
    }
    
    public String toString() {
        return "("+first.toString()+","+second.toString()+","+third.toString()+")";
    }
}

