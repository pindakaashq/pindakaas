package savilerow.expression;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2020 Peter Nightingale
    
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

//  Pseudo-boolean with at-most-one groups constraint. 
//  Third child is a number to control the encoding: 1 means use MDD, 2 GPW, 3 SWC, 4 GGT, 5 RGGT, 6 GGTH

public class EOPB extends AMOPB {
    public static final long serialVersionUID = 1L;
    
    public EOPB(ASTNode mat, ASTNode k, ASTNode enc, boolean _fromPB) {
        super(mat, k, enc, _fromPB);
    }
    
    public ASTNode copy() {
        return new EOPB(getChild(0), getChild(1), getChild(2), fromPB);
    }
    
    @Override
    public ASTNode simplify() {
        return super.simplify(false);
    }
}
