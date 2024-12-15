package savilerow;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Saad Attieh
    
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
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

public class Permutation {
    private static ArrayList<String> ordering = null;
    private Map<String, String> mappings = new HashMap<String, String>();

    public void addMapping(String key, String value) {
        mappings.put(key, value);
    }

    public ArrayList<String> permutate() {
        if (ordering == null)
            throw new IllegalStateException(
                    "An initial ordering has not been set for permutations.  An initial ordering must be set before a permutation can be applied.");
        ArrayList<String> permutatedVars = new ArrayList<String>();
        for (String var : ordering) {
            if (mappings.containsKey(var))
                permutatedVars.add(mappings.get(var));
            else
                permutatedVars.add(var);
        }
        return permutatedVars;
    }

    public static void setOrdering(Collection<String> ordering) {
        if (ordering == null)
            return;
        Permutation.ordering = new ArrayList<String>(ordering);
    }

    public static ArrayList<String> getOrdering() {
        return ordering;
    }
}