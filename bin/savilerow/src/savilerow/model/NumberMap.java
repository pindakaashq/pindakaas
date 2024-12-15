package savilerow.model;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Patrick Spracklen and Peter Nightingale
    
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


import java.util.Objects;

public class NumberMap {
    private long value;
    private String variable;
    
    public NumberMap(long Value, String variable)
    {
        this.value=Value;
        this.variable=variable;
    }
    
    @Override
    public int hashCode()
    {
        return Objects.hash(variable, value);
    }
    
    @Override
    public boolean equals(Object object)
    {
        if (!(object instanceof NumberMap))
            return false;
        if (object == this)
            return true;

        NumberMap currentObject=(NumberMap) object;

        return (this.variable.equals(currentObject.variable)) && this.value==currentObject.value;
    }

    public String getVariable()
    {
        return variable;
    }

    public long getValue()
    {
        return value;
    }
    
    public String toString() {
        return "("+variable+", "+value+")";
    }
}
