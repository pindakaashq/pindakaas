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


import java.io.BufferedWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

import savilerow.CmdFlags;
import savilerow.model.*;

public class Xor extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    public Xor(ArrayList<ASTNode> ch) {
        super(ch);
    }

    // Ctor to help replace binop.
    public Xor(ASTNode l, ASTNode r) {
        super(l, r);
    }
    
    public Xor(ASTNode[] ch) {
        super(ch);
    }

    public ASTNode copy() {
        return new Xor(getChildrenArray());
    }
    public boolean isRelation() { return true; }
    public boolean strongProp() {
        for(int i=0; i<numChildren(); i++) {
            if(!getChild(i).strongProp()) {
                return false;
            }
        }
        return true;
    }
    
    public ASTNode simplify() {
        boolean changed = false;
        
        ArrayList<ASTNode> ch = getChildren();
        if(!CmdFlags.getOutputReady()) {
            //  Collect nested XOR into here.
            for (int i =0; i < ch.size(); i++) {
                if (ch.get(i) instanceof Xor) {
                    changed = true;
                    ASTNode curnode = ch.remove(i);
                    i--;                // current element removed so move back in list.
                    // Add children to end of this list, so that the loop will process them.
                    ch.addAll(curnode.getChildren());
                }
            }
        }
        
        // Constant folding
        boolean collectConstant=false;
        int collected=0;
        for (int i =0; i < ch.size(); i++) {
            if (ch.get(i).isConstant()) {
                long val = ch.get(i).getValue();
                collectConstant=collectConstant ^ (val==1);
                collected++;
                ch.remove(i);
                i--;
            }
        }
        if(collected>0) {
            if(collectConstant) {
                ch.add(new BooleanConstant(true));   //  Only add if 1 -- no reason to have a 0 constant. 
            }
        }
        if(collected>1 || (collected==1 && !collectConstant)) {
            changed=true;
        }
        
        // remove duplicates
        
        HashMap<ASTNode,Integer> a = new HashMap<ASTNode,Integer>();
        for(int i=0; i<ch.size(); i++) {
            ASTNode child=ch.get(i);
            if(a.containsKey(child)) {
                // Remove the two identical entries
                int idx1=a.get(child);
                ch.remove(i);
                ch.remove(idx1);
                // Take the entry out of the hash table.
                a.remove(child);
                i=i-2;   // Step back in the iteration
            }
            else {
                a.put(child, i);
            }
        }
        
        if (ch.size() == 0) {
            return new BooleanConstant(false);
        }
        if (ch.size() == 1) {
            ch.get(0).setParent(null);
            return ch.get(0);
        }
        if (changed) {
            for(int i=0; i<ch.size(); i++) {
                ch.get(i).setParent(null);
            }
            return new Xor(ch);
        }
        return null;
    }

    // If contained in a Negate, push the negation inside by adding a constant 1.
    @Override
    public boolean isNegatable() {
        return true;
    }
    @Override
    public ASTNode negation() {
        ArrayList<ASTNode> ch = getChildren();
        ch.add(new BooleanConstant(true));
        return new Xor(ch);
    }
    
    public boolean typecheck(SymbolTable st) {
        for (ASTNode child : getChildren()) {
            if (!child.typecheck(st)) {
                return false;
            }
            if (!child.isRelation()) {
                System.out.println("ERROR: 'Xor' contains something other than a relation:" + child);
                return false;
            }
        }
        return true;
    }

    public ASTNode normalise() {
        // sort by hashcode
        ArrayList<ASTNode> ch = getChildren();
        boolean changed = sortByHashcode(ch);
        
        if (changed) {
            return new Xor(ch);
        } else {
            return this;
        }
    }
    
    public ASTNode normaliseAlpha() {
        // sort by hashcode
        ArrayList<ASTNode> ch = getChildren();
        boolean changed = sortByAlpha(ch);
        
        if (changed) {
            return new Xor(ch);
        } else {
            return null;
        }
    }
    
    public boolean isCommAssoc() {
        return true;
    }
    
    public String toString() {
        StringBuilder b = new StringBuilder();
        b.append("(");
        for (int i =0; i < numChildren(); i++) {
            b.append(getChild(i).toString());
            if (i < numChildren() - 1) {
                b.append(" xor ");
            }
        }
        b.append(")");
        return b.toString();
    }
    
    public void toMinion(BufferedWriter b, boolean bool_context) throws IOException
    {
        assert bool_context;
        b.append("diseq(");
        getChild(0).toMinion(b, false);
        b.append(", ");
        getChild(1).toMinion(b, false);
        b.append(")");
    }
    public void toFlatzinc(BufferedWriter b, boolean bool_context) throws IOException {
        b.append("constraint bool_xor(");
        getChild(0).toFlatzinc(b, true);
        b.append(",");
        getChild(1).toFlatzinc(b, true);
        b.append(");");
    }
    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("(");
        getChild(0).toMinizinc(b, true);
        b.append(" xor ");
        getChild(1).toMinizinc(b, true);
        b.append(")");
    }
    
    public void toSAT(Sat satModel) throws IOException {
        assert numChildren()==2;
        ternaryXorEncode(satModel, getChild(0).directEncode(satModel, 1), getChild(1).directEncode(satModel, 1), satModel.getTrue());
    }
    
    public void toSATWithAuxVar(Sat satModel, long auxVar) throws IOException {
        assert numChildren()==2;
        ternaryXorEncode(satModel, getChild(0).directEncode(satModel, 1), getChild(1).directEncode(satModel, 1), auxVar);
    }
    
    private void ternaryXorEncode(Sat satModel, long a, long b, long aux) throws IOException {
        // Rule out the four disallowed assignments.
        satModel.addClause(-a, -b, -aux);
        satModel.addClause(-a, b, aux);
        satModel.addClause(a, -b, aux);
        satModel.addClause(a, b, -aux);
    }
    
    @Override
    public boolean childrenAreSymmetric() {
        return true;
    }
}