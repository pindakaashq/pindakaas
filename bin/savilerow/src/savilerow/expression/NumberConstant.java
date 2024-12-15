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


public abstract class NumberConstant extends ASTNode {
    public static final long serialVersionUID = 1L;
    
    
    public static NumberConstant make(long num) {
        if(num>=Byte.MIN_VALUE && num<=Byte.MAX_VALUE) {
            return new NumberConstantByte((byte) num);
        }
        else if(num>=Integer.MIN_VALUE && num<=Integer.MAX_VALUE) {
            return new NumberConstantInt((int) num);
        }
        else {
            return new NumberConstantLong(num);
        }
    }
    
    public boolean isConstant() {
        return true;
    }
    public boolean isNumerical() {
        return true;
    }
    public boolean usesSMTEncoding() {
        return true;
    }
    public boolean canVariableEncode() {
        return true;
    }
}