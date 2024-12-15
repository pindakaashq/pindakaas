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

//  A bracketed expression -- needed to check for things like A<B<C  vs  A<(B<C)

public class Brackets extends Unary
{
    public static final long serialVersionUID = 1L;
    public Brackets(ASTNode a) {
        super(a);
    }
    
    public ASTNode copy() {
        return new Brackets(getChild(0));
    }
    
    public ASTNode simplify() {
        //  Simplify away immediately; this class is only for checking assoc of binary operators. 
        getChild(0).setParent(null);
        return getChild(0);
    }
    
    public boolean toFlatten(boolean propagate) {
        return false;
    }
    public boolean isNumerical() {
        return getChild(0).isNumerical();
    }
    public boolean isRelation() {
        return getChild(0).isRelation();
    }
    public boolean isConstant() {
        return getChild(0).isConstant();
    }
    public int getCategory() {
        return getChild(0).getCategory();
    }
    public int getDimension() {
        return getChild(0).getDimension();
    }
    
    //  These tuple methods are probably not needed but implemented just in case. 
    public boolean isTuple() {
        return getChild(0).isTuple();
    }
    public int getTupleLength() {
        return getChild(0).getTupleLength();
    }
    public long getValueIdx(int idx) {
        return getChild(0).getValueIdx(idx);
    }
    
    public long getValue() {
        return getChild(0).getValue();
    }
    
    //  Set description pass-throughs. 
    public boolean isSet() {
        return getChild(0).isSet();
    }
    public boolean isFiniteSet() {
        return getChild(0).isFiniteSet();
    }
    public boolean isFiniteSetUpper() {
        return getChild(0).isFiniteSetUpper();
    }
    public boolean isFiniteSetLower() {
        return getChild(0).isFiniteSetLower();
    }
    public boolean isBooleanSet() {
        return getChild(0).isBooleanSet();
    }
    public boolean isIntegerSet() {
        return getChild(0).isIntegerSet();
    }
    public boolean isConstantSet() {
        return getChild(0).isConstantSet();
    }
    
    public boolean isRegularMatrix() {
        return getChild(0).isRegularMatrix();
    }
    public boolean isMatrixLiteral() {
        return getChild(0).isMatrixLiteral();
    }
    public ArrayList<ASTNode> getIndexDomains() {
        return getChild(0).getIndexDomains();
    }
    public ArrayList<ASTNode> getIndexDomainsIrregular() {
        return getChild(0).getIndexDomainsIrregular();
    }
    
    public String toString()
    {
        return "("+getChild(0)+")";
    }
    
    public Intpair getBounds() {
        return getChild(0).getBounds();
    }
    public ArrayList<Intpair> getIntervalSet() {
        return getChild(0).getIntervalSet();
    }
    public ArrayList<Intpair> getIntervalSetExp() {
        return getChild(0).getIntervalSetExp();
    }
    
    //  Probably not needed but for the sake of completeness...
    @Override
    public boolean inTopConjunction() {
        return getParent().inTopConjunction();
    }
    @Override
    public boolean inTopAnd() {
        return getParent().inTopAnd();
    }
    
    
}
