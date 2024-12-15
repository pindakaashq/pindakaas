package savilerow.model;
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

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Objects;

public class replaces_matrix_entry implements Serializable {
    private static final long serialVersionUID = 1L;
    public replaces_matrix_entry(String s, ArrayList<Long> i) {name=s; idx=i;}
    public String name;   // name of matrix
    public ArrayList<Long> idx;  // indices that this var corresponds to. 
    
    @Override
    public boolean equals(Object o) {
        if(! (o instanceof replaces_matrix_entry)) return false;
        replaces_matrix_entry c=(replaces_matrix_entry)o;
        if(! c.name.equals(name)) return false;
        if(! c.idx.equals(idx)) return false;
        return true;
    }
    
    @Override public int hashCode() {
        return Objects.hash(name, idx);
    }
}
