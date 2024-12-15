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
import java.util.Objects;

public class categoryentry implements Serializable {
    private static final long serialVersionUID = 1L;
    categoryentry(String nam, int c, categoryentry p, categoryentry n) {
        name=nam; cat=c; prev=p; next=n;
        already_written = false;
    }
    public String name;
    public int cat;
    public boolean already_written;
    public categoryentry prev;
    public categoryentry next;
    
    @Override
    public boolean equals(Object b) {
        if(! (b instanceof categoryentry)) return false;
        categoryentry c=(categoryentry) b;
        if(! c.name.equals(this.name)) return false;
        if( c.cat!= this.cat) return false;
        return true;
    }
    
    @Override public int hashCode() {
        return Objects.hash(name, cat);
    }
}
