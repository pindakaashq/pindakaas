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
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;

import savilerow.*;
import savilerow.model.*;

public class WeightedSum extends ASTNodeC {
    public static final long serialVersionUID = 1L;
    long[] weights;
    
    public WeightedSum(ArrayList<ASTNode> ch) {
        super(ch);
        
        weights= new long[ch.size()];
        for (int i =0; i < ch.size(); i++) {
            weights[i]=1L;
        }
    }
    public WeightedSum(ASTNode[] ch) {
        super(ch);
        
        weights= new long[ch.length];
        for (int i =0; i < ch.length; i++) {
            weights[i]=1L;
        }
    }
    
    public WeightedSum(ArrayList<ASTNode> ch, ArrayList<Long> w) {
        super(ch);
        weights=new long[w.size()];
        for(int i=0; i<w.size(); i++) weights[i]=w.get(i);
        
        assert ch.size() == w.size();
    }
    
    // More efficient ctor taking arrays.
    // The arrays passed in here are not copied, so must not be altered by the calling
    // method after construction. 
    public WeightedSum(ASTNode[] ch, long[] w) {
        super(ch);
        weights = w;
        assert ch.length == w.length;
    }
    
    // ctor avoids having to make an arraylist if there are only two children.
    public WeightedSum(ASTNode a, ASTNode b) {
        super(a, b);
        weights = new long[2];
        weights[0]=1L;
        weights[1]=1L;
    }
    
    public WeightedSum(ASTNode a, ASTNode b, long aweight, long bweight) {
        super(a, b);
        weights=new long[2];
        weights[0]=aweight;
        weights[1]=bweight;
    }
    
    public WeightedSum(ASTNode a, long aweight) {
        super(a);
        weights=new long[1];
        weights[0]=aweight;
    }
    
    public ArrayList<Long> getWeights() {
        ArrayList<Long> l = new ArrayList<Long>(weights.length);
        for(int i=0; i<weights.length; i++) l.add(weights[i]);
        return l;
    }
    public long[] getWeightsArray() {
        long[] l = new long[weights.length];
        System.arraycopy(weights, 0, l, 0, weights.length);
        return l;
    }
    // Like getChild
    public long getWeight(int i) {
        return weights[i];
    }

    public ASTNode copy() {
        long[] wts=new long[weights.length];
        for(int i=0; i<weights.length; i++) wts[i]=weights[i];
        return new WeightedSum(getChildrenArray(), wts);
    }
    @Override
    public boolean equals(Object other) {
        if (! (other instanceof WeightedSum)) {
            return false;
        }
        WeightedSum oth = (WeightedSum) other;

        if (! oth.getChildren().equals(getChildren())) {
            return false;
        }
        if (! Arrays.equals(oth.weights, weights)) {
            return false;
        }

        return true;
    }
    
    @Override
    public int hashCode() {
        if(hashCache==Integer.MIN_VALUE) {
            int hash = Arrays.hashCode(weights);
            hash = hash * 13 + Arrays.hashCode(getChildrenArray());
            hashCache=hash;  // store
            return hash;
        }
        else {
            return hashCache;
        }
    }
    
    @Override
    public boolean strongProp() {
        for(int i=0; i<numChildren(); i++) {
            Intpair b=getChild(i).getBounds();
            if(b.upper-b.lower>1 || !getChild(i).strongProp()) {
                return false;
            }
        }
        return true;
    }
    
    //  Pair class used for sorting terms in the sum.
    class ASTLongPair implements Comparable<ASTLongPair> {
        public long wt;
        public ASTNode ch;
        public ASTLongPair(long _wt, ASTNode _ch) {
            wt=_wt;
            ch=_ch;
        }
        public int compareTo(ASTLongPair o) {
            int h1=ch.hashCode();
            int h2=o.ch.hashCode();
            if(h1<h2) {
                return -1;
            }
            else if(h1==h2) {
                return 0;
            }
            else {
                return 1;
            }
        }
        public String toString() {
            return "("+wt+", "+ch+")";
        }
    }
    
    //  Pair class used for sorting terms in the sum.
    class ASTLongPairAlpha implements Comparable<ASTLongPairAlpha> {
        public long wt;
        public ASTNode ch;
        public ASTLongPairAlpha(long _wt, ASTNode _ch) {
            wt=_wt;
            ch=_ch;
        }
        public int compareTo(ASTLongPairAlpha o) {
            return ch.toString().compareTo(o.ch.toString());
        }
        public String toString() {
            return "("+wt+", "+ch+")";
        }
    }
    
    // Similar to one from And / Or
    public ASTNode simplify() {
        ArrayList<ASTNode> ch = getChildren();
        ArrayList<Long> wts = getWeights();
        boolean changed = false;        // has it changed -- do we return a new WeightedSum?
        
        assert ch.size() == wts.size();
        // Collect children (and children's children etc) into this.
        for (int i =0; i < ch.size(); i++) {
            if (ch.get(i) instanceof WeightedSum) {
                ASTNode curnode = ch.remove(i);
                long weight = wts.remove(i);
                i--;                // current element removed so move back in list.
                // Add children to end of this list, so that the loop will process them.

                ch.addAll(curnode.getChildren());
                ArrayList<Long> curnode_weights = ((WeightedSum) curnode).getWeights();
                for (int j =0; j < curnode_weights.size(); j++) {
                    wts.add(curnode_weights.get(j) * weight);
                }
                changed = true;
                continue;
            }
            if (ch.get(i) instanceof UnaryMinus) {
                changed = true;
                ch.set(i, ch.get(i).getChild(0));                // get the child of the (-)
                wts.set(i, -wts.get(i));                // Negate the weight.
            }
        }
        assert ch.size() == wts.size();
        
        // Constant folding
        // Is there more than one constant
        int numConstants=0; 
        int constIdx=-1;
        for (int i =0; i < ch.size(); i++) {
            if (ch.get(i).isConstant()) {
                if(ch.get(i).getValue()*wts.get(i)==0) {
                    //  Value 0 -- Just remove it.
                    ch.remove(i); wts.remove(i);
                    i--;
                    changed=true;
                }
                else {
                    constIdx=i;
                    numConstants++;
                }
            }
        }
        
        if(numConstants>0) {
            if(numConstants==1) {
                //  Put in the normal form which is a weight of 1.
                if(wts.get(constIdx)!=1) {
                    ch.set(constIdx, NumberConstant.make(ch.get(constIdx).getValue() * wts.get(constIdx)));
                    wts.set(constIdx, 1L);
                    changed=true;
                }
            }
            else {
                //  if numConstants>1, collect them.
                int newConstant=0;
                for (int i =0; i < ch.size(); i++) {
                    if (ch.get(i).isConstant()) {
                        newConstant += ch.get(i).getValue() * wts.get(i);
                        ch.remove(i); wts.remove(i); i--;
                    }
                }
                if (ch.size() == 0) {
                    return NumberConstant.make(newConstant);
                }
                if (newConstant != 0) {
                    ch.add(NumberConstant.make(newConstant));
                    wts.add(1L);
                    changed=true;
                }
            }
        }
        
        // Sort by hashcode before removing duplicates
        boolean isSorted=true;
        for(int i=0; i<ch.size()-1; i++) {
            if(ch.get(i).hashCode()>ch.get(i+1).hashCode()) {
                isSorted=false;
                break;
            }
        }
        
        if(!isSorted) {
            ASTLongPair[] tosort=new ASTLongPair[ch.size()];
            for(int i=0; i<ch.size(); i++) {
                tosort[i]=new ASTLongPair(wts.get(i), ch.get(i));
            }
            
            Arrays.sort(tosort);
            
            for(int i=0; i<ch.size(); i++) {
                ch.set(i, tosort[i].ch);
                wts.set(i, tosort[i].wt);
            }
            changed=true;
        }
        
        // remove dups.
        for (int i =0; i < ch.size() - 1; i++) {
            if (ch.get(i).equals(ch.get(i + 1))) {
                changed = true;
                ch.remove(i + 1);
                wts.set(i, wts.get(i) + wts.remove(i + 1));
                i--;
            }
        }
        
        // Discard 0-weighted children.
        for (int i =0; i < ch.size(); i++) {
            if (wts.get(i) == 0) {
                changed = true;
                wts.remove(i);
                ch.remove(i);
                i--;
            }
        }
        
        if (ch.size() == 0) {
            return NumberConstant.make(0);
        }
        if (ch.size() == 1 && wts.get(0) == 1) {
            //  Odd case -- may return something of type bool instead of int. 
            return ch.get(0);
        }
        if (ch.size() == 1 && wts.get(0) == -1) {
            return new UnaryMinus(ch.get(0));
        }
        if (changed) {
            for(int i=0; i<ch.size(); i++) ch.get(i).setParent(null);
            return new WeightedSum(ch, wts);
        }
        return null;
    }
    public boolean typecheck(SymbolTable st) {
        for (int i =0; i < numChildren(); i++) {
            if (!getChild(i).typecheck(st)) {
                return false;
            }
            if (getChild(i).getDimension() > 0) {
                CmdFlags.println("ERROR: Unexpected matrix in weighted sum: " + this);
                return false;
            }
        }
        return true;
    }
    
    // Sort by hashcode
    public ASTNode normalise() {
        boolean isSorted=true;
        for(int i=0; i<numChildren()-1; i++) {
            if(getChild(i).hashCode()>getChild(i+1).hashCode()) {
                isSorted=false;
                break;
            }
        }
        
        if(!isSorted) {
            ASTLongPair[] tosort=new ASTLongPair[numChildren()];
            for(int i=0; i<numChildren(); i++) {
                tosort[i]=new ASTLongPair(weights[i], getChild(i));
            }
            
            Arrays.sort(tosort);
            
            for(int i=0; i<numChildren(); i++) {
                tosort[i].ch.setParent(null); //  Do not copy it on next line.
                setChild(i, tosort[i].ch);
                weights[i]=tosort[i].wt;
            }
        }
        return this;
    }
    
    public ASTNode normaliseAlpha() {
        // Sort by hashcode before removing duplicates
        boolean isSorted=true;
        for(int i=0; i<numChildren()-1; i++) {
            if(getChild(i).toString().compareTo(getChild(i+1).toString())>0) {
                isSorted=false;
                break;
            }
        }
        
        if(!isSorted) {
            ASTLongPairAlpha[] tosort=new ASTLongPairAlpha[numChildren()];
            for(int i=0; i<numChildren(); i++) {
                tosort[i]=new ASTLongPairAlpha(weights[i], getChild(i));
            }
            
            Arrays.sort(tosort);
            
            for(int i=0; i<numChildren(); i++) {
                tosort[i].ch.setParent(null); //  Do not copy it on next line.
                setChild(i, tosort[i].ch);
                weights[i]=tosort[i].wt;
            }
        }
        return null;
    }

    public boolean isCommutative() {
        return true;
    }

    public boolean isAssociative() {
        return true;
    }

    public String toString() {
        StringBuilder b=new StringBuilder();
        b.append("(");
        for (int i =0; i < numChildren(); i++) {
            if(weights[i]==1 || weights[i]==-1) {
                if(i>0 && weights[i]==1) {
                    b.append(" + ");
                }
                if(weights[i]==-1) {
                    b.append(" - ");
                }
                b.append(getChild(i).toString());
            }
            else {
                if(i>0 && weights[i]>0) {
                    b.append(" + ");
                }
                if(weights[i]<0) {
                    b.append(" - ");
                }
                
                if(weights[i]>=0) {
                    b.append(weights[i]);
                }
                else {
                    b.append(-weights[i]);
                }
                b.append("*");
                b.append(getChild(i).toString());
            }
        }
        b.append(")");
        return b.toString();
    }

    public boolean toFlatten(boolean propagate) {
        if (getParent() instanceof LessEqual) {
            return false;            // Will be output as sumleq or sumgeq. Only one child of <= can be a sum. 
        }
        return true;
    }
    public boolean isNumerical() {
        return true;
    }
    
    public Intpair getBounds() {
        // Add up all the lower bounds and upper bounds of each term.
        BigInteger lower = BigInteger.valueOf(0L);
        BigInteger upper = BigInteger.valueOf(0L);
        for (int i =0; i < weights.length; i++) {
            Intpair a = getChild(i).getBounds();
            if (weights[i] > 0) {
                lower = lower.add(BigInteger.valueOf(a.lower).multiply(BigInteger.valueOf(weights[i])));
                upper = upper.add(BigInteger.valueOf(a.upper).multiply(BigInteger.valueOf(weights[i])));
            }
            else {
                lower = lower.add(BigInteger.valueOf(a.upper).multiply(BigInteger.valueOf(weights[i])));
                upper = upper.add(BigInteger.valueOf(a.lower).multiply(BigInteger.valueOf(weights[i])));
            }
        }
        
        return new Intpair(Intpair.BigIntegerToLong(lower), Intpair.BigIntegerToLong(upper));
    }
    
    public ArrayList<Intpair> getIntervalSetExp() {
        //  Use intervallim as a limit on the number of intervals here, not the size of the returned set.
        ArrayList<Intpair> out=new ArrayList<Intpair>();
        out.add(new Intpair(0,0));  // Start with the identity
        
        for(int i=0; i<weights.length; i++) {
            ArrayList<Intpair> tmp=getChild(i).getIntervalSetExp();
            
            if( (weights[i]>1 || weights[i]<-1) && Intpair.numValues(tmp)> Constants.intervallim) {
                tmp=Intpair.scaleIntervalSet(tmp, weights[i]);  // Avoid blow-up by approximating the set. 
            }
            else {
                tmp=Intpair.multIntervalSet(tmp, weights[i]);  //  This can blow up into d intervals.
            }
            
            if(tmp.size()>Constants.intervallim) {
                return super.getIntervalSetExp();
            }
            
            // Add each interval from out to each interval in tmp
            ArrayList<Intpair> out2=new ArrayList<Intpair>();
            
            for(int j=0; j<out.size(); j++) {
                for(int k=0; k<tmp.size(); k++) {
                    long lower=out.get(j).lower+tmp.get(k).lower;
                    long upper=out.get(j).upper+tmp.get(k).upper;
                    out2.add(new Intpair(lower, upper));
                }
            }
            
            Intpair.normalise(out2);
            out=out2;
            
            if(out.size()>Constants.intervallim) {
                return super.getIntervalSetExp();
            }
        }
        
        return out;
    }
    
    public long getValue() {
        // Should only be called in typecheck, before simplify
        long accumulator =0;
        for (int i =0; i < numChildren(); i++) {
            assert getChild(i).isConstant();
            accumulator += getChild(i).getValue() * weights[i];
        }
        return accumulator;
    }

    public Pair<ASTNode, ASTNode> retrieveConstant() {
        // Split the weighted sum into the constant part and the variable part.
        // Assumes it's simplified so only one constant.
        for (int i =0; i < numChildren(); i++) {
            if (getChild(i).isConstant()) {
                ArrayList<ASTNode> ch = getChildren();
                ArrayList<Long> wts = getWeights();

                ASTNode constant = ch.remove(i);
                Long weight = wts.remove(i);
                constant = NumberConstant.make(constant.getValue() * weight);

                return new Pair<ASTNode, ASTNode>(constant, new WeightedSum(ch, wts));
            }
        }
        return null;
    }
    
    public Pair<ASTNode, ASTNode> factorOutGCD() {
        // Calculate the GCD of the weights and return it and a sum with that divided out. 
        // First check for the very common case of 1's.
        
        boolean containsOne=false;
        
        for(int i=0; i<numChildren(); i++) {
            if(weights[i]==1L || weights[i]==-1L) {
                containsOne=true;
                break;
            }
        }
        
        long lgcd;
        if(containsOne) {
            lgcd=1;
        }
        else {
            BigInteger gcd=BigInteger.valueOf(weights[0]);
            
            for(int i=1; i<numChildren(); i++) {
                gcd=gcd.gcd(BigInteger.valueOf(weights[i]));
            }
            
            lgcd=gcd.longValue();
        }
        
        if(lgcd>1) {
            // Divide through by the GCD.
            
            long[] newweights=new long[weights.length];
            ASTNode[] newch=new ASTNode[weights.length];
            for(int i=0; i<numChildren(); i++) {
                newweights[i]=weights[i]/lgcd;
                newch[i]=getChild(i);
            }
            
            return new Pair<ASTNode, ASTNode>(NumberConstant.make(lgcd), new WeightedSum(newch, newweights));
        }
        return null;
    }
    
    @Override
    public int polarity(int child) {
        if(weights[child]<0) {
            return -polarity();
        }
        else {
            return polarity();
        }
    }
    
    //////////////////////////////////////////////////////////////////////////// 
    // 
    // Output methods.
    
    // These may also be called from LessEqual.
    public void toMinionLeq(BufferedWriter b, ASTNode aux) throws IOException {
        boolean all1weights = true;
        for (int i =0; i < weights.length; i++) {
            if (weights[i] != 1) {
                all1weights = false;
                break;
            }
        }

        if (all1weights) {
            b.append("sumleq([");
            for (int i =0; i < numChildren(); i++) { getChild(i).toMinion(b, false); if (i < numChildren() - 1) {
                    b.append(",");
                }
            }
            b.append("],");
            aux.toMinion(b, false);
            b.append(")");
        } else {
            b.append("weightedsumleq([");
            for (int i =0; i < weights.length; i++) { b.append(String.valueOf(weights[i])); if (i < weights.length - 1) {
                    b.append(",");
                }
            }
            b.append("],[");
            for (int i =0; i < numChildren(); i++) { getChild(i).toMinion(b, false); if (i < numChildren() - 1) {
                    b.append(",");
                }
            }
            b.append("],");
            aux.toMinion(b, false);
            b.append(")");
        }
    }

    public void toMinionGeq(BufferedWriter b, ASTNode aux) throws IOException {
        boolean all1weights = true;
        for (int i =0; i < weights.length; i++) {
            if (weights[i] != 1) {
                all1weights = false;
                break;
            }
        }

        if (all1weights) {
            b.append("sumgeq([");
            for (int i =0; i < numChildren(); i++) { getChild(i).toMinion(b, false); if (i < numChildren() - 1) {
                    b.append(",");
                } }
            b.append("],");
            aux.toMinion(b, false);
            b.append(")");
        } else {
            b.append("weightedsumgeq([");
            for (int i =0; i < weights.length; i++) { b.append(String.valueOf(weights[i])); if (i < weights.length - 1) {
                    b.append(",");
                } }
            b.append("],[");
            for (int i =0; i < numChildren(); i++) { getChild(i).toMinion(b, false); if (i < numChildren() - 1) {
                    b.append(",");
                } }
            b.append("],");
            aux.toMinion(b, false);
            b.append(")");
        }
    }

    // Flatzinc ones.
    public void toFlatzincLeq(BufferedWriter b, ASTNode aux) throws IOException {
        b.append("constraint int_lin_le([");
        for (int i =0; i < weights.length; i++) { b.append(String.valueOf(weights[i])); b.append(","); }
        b.append("-1],[");
        for (int i =0; i < numChildren(); i++) { getChild(i).toFlatzinc(b, false); b.append(","); }
        aux.toFlatzinc(b, false);        // put aux var into sum, with weight -1
        b.append("],0);");        // le 0.
    }


    public void toFlatzincGeq(BufferedWriter b, ASTNode aux) throws IOException {
        b.append("constraint int_lin_le([");
        for (int i =0; i < weights.length; i++) { b.append(String.valueOf(-weights[i])); b.append(","); }
        b.append("1],[");
        for (int i =0; i < numChildren(); i++) { getChild(i).toFlatzinc(b, false); b.append(","); }
        aux.toFlatzinc(b, false);        // put into sum with weight 1.
        b.append("],0);");
    }

    public void toFlatzincWithAuxVar(BufferedWriter b, ASTNode aux) throws IOException {
        if(! aux.isConstant()) {
            // Rearrange to put 0 on right hand side. 
            b.append("constraint int_lin_eq([");
            for (int i =0; i < weights.length; i++) { b.append(String.valueOf(weights[i])); b.append(","); }
            b.append("-1],[");
            for (int i =0; i < numChildren(); i++) { getChild(i).toFlatzinc(b, false); b.append(","); }
            aux.toFlatzinc(b, false);
            b.append("],0);");
        }
        else {
            // Already constant on right hand side. 
            b.append("constraint int_lin_eq([");
            for (int i =0; i < weights.length; i++) { 
                b.append(String.valueOf(weights[i]));
                if(i<weights.length-1) b.append(",");
            }
            b.append("],[");
            for (int i =0; i < numChildren(); i++) { 
                getChild(i).toFlatzinc(b, false);
                if(i<weights.length-1) b.append(","); 
            }
            b.append("],");
            aux.toFlatzinc(b, false);
            b.append(");");
        }
    }

    public void toMinizinc(StringBuilder b, boolean bool_context) {
        b.append("(");
        for (int i =0; i < numChildren(); i++) {
            b.append("(");
            if (weights[i] != 1) {
                b.append(weights[i]);
                b.append("*");
            }
            getChild(i).toMinizinc(b, false);
            b.append(")");
            if (i < numChildren() - 1) {
                b.append("+");
            }
        }
        b.append(")");
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //  SAT encoding
    
    //  Order encoding exactly following Jeavons and Petke.
    //  w is a local copy of weights, possibly adjusted by the calling method.
    private void orderEncodingLeq(Sat satModel, long[] w, long leqValue, long aux) throws IOException {
        long[] tuple=new long[numChildren()];
        
        // Find set of intervals of each term. 
        ArrayList<ArrayList<Intpair>> ranges=new ArrayList<ArrayList<Intpair>>();
        
        for(int i=0; i<numChildren(); i++) {
            ArrayList<Intpair> l=getChild(i).getIntervalSetExp();
            l=Intpair.multIntervalSet(l, w[i]);
            ranges.add(l);
        }
        
        ArrayList<ASTNode> ch=getChildren();
        // Sort ch by ranges size. 
        for(int i=0; i<numChildren(); i++) {
            for(int j=i-1; j>=0; j--) {
                if (Intpair.numValues(ranges.get(j + 1)) < Intpair.numValues(ranges.get(j))) {
                    // swap
                    ASTNode tmp = ch.get(j + 1);
                    ch.set(j + 1, ch.get(j));
                    ch.set(j, tmp);
                    
                    long tmp2 = w[j+1];
                    w[j + 1]=w[j];
                    w[j]=tmp2;
                    
                    ArrayList<Intpair> temp=ranges.get(j+1);
                    ranges.set(j + 1, ranges.get(j));
                    ranges.set(j, temp);
                } else {
                    break;
                }
            }
        }
        
        orderEncodingLeqHelper(satModel, ch, w, leqValue, ranges, tuple, 0, aux);
    }
    
    // Tuple contains domain values.
    // Writes out clauses like:
    //    2x -2y  + 3z <= 12
    
    //   forall a in D(x), forall b in D(y). 
    
    //  ( 2x=2 /\ -2y=4 ) -> 3z<=6
    //  ( 2x>=2 /\ -2y>=4 ) -> 3z<=6
    //    2x<2 \/ -2y<4 \/ 3z<=6
    //    x<1  \/  y>-2 \/ z<=2   (divide by weights,  reverse comparison when weight is neg)
    //    x<=0   \/  y>-2  \/  z<=2
    
    private void orderEncodingLeqHelper(Sat satModel, ArrayList<ASTNode> ch, long[] w, long leqValue, ArrayList<ArrayList<Intpair>> ranges, long[] tuple, int pos, long aux) throws IOException {
        if(pos==ch.size()-1) {
            // Base case. Calculate the value of the final variable and add a clause. 
            boolean clauseTrue=false;
            long sum=0;
            for(int i=0; i<ch.size()-1; i++) sum+=tuple[i];
            
            tuple[pos]=leqValue-sum;
            
            if(tuple[pos]>ranges.get(pos).get(ranges.get(pos).size()-1).upper) {
                return;  // bail out if tuple[pos] is larger than the upper bound of the final term
            }
            
            ArrayList<Long> clause=new ArrayList<Long>(ch.size());
            if(aux!=0) clause.add(aux);
            
            for(int i=0; i<ch.size()-1; i++) {
                //  From the value of the term to the value of the SR variable.
                //long addlit=(new MultiplyMapper(getChild(i), NumberConstant.make(w[i]))).orderEncode(satModel, tuple[i]-1);   // Strictly less
                
                long val=tuple[i]/w[i];   //  There must be no remainder.
                assert tuple[i]%w[i]==0;
                long addlit;
                if(w[i]>0) {
                    addlit=ch.get(i).orderEncode(satModel, val-1);
                }
                else {
                    addlit=-ch.get(i).orderEncode(satModel, val);
                }
                
                // If new literal is true, 
                if(addlit==satModel.getTrue()) {
                    clauseTrue=true;
                    break;
                }
                
                // If new literal is not false, add to clause. 
                if(addlit != -satModel.getTrue()) {
                    clause.add(addlit);
                }
            }
            // The final one is different
            //long addlit=(new MultiplyMapper(getChild(pos), NumberConstant.make(w[pos]))).orderEncode(satModel, tuple[pos]);
            long addlit;
            if(w[pos]>0) {
                long val=Divide.div(tuple[pos], w[pos]);  // Floor division.
                addlit=ch.get(pos).orderEncode(satModel, val);
            }
            else {
                // e.g. -3z<=7  ->  z >= -7/3  ->  z>=-2.333   ->  z>=-2  -> z>-3
                // e.g. -3z<=6  ->  z >= -6/3  ->  z>=-2       ->            z>-3
                long val=Divide.divceil(tuple[pos], w[pos]);
                addlit=-ch.get(pos).orderEncode(satModel, val-1);
            }
            if(addlit==satModel.getTrue()) {
                clauseTrue=true;
            }
            if(addlit!=-satModel.getTrue()) {
                clause.add(addlit);
            }
            
            if(!clauseTrue) satModel.addClause(clause);
            
        }
        else {
            ArrayList<Intpair> intervals=ranges.get(pos);
            for(int i=0; i<intervals.size(); i++) {
                
                for(long val=intervals.get(i).lower; val<=intervals.get(i).upper; val++) {
                    tuple[pos]=val;
                    orderEncodingLeqHelper(satModel, ch, w, leqValue, ranges, tuple, pos+1, aux);
                }
            }
        }
    }
    
    //  Exact impl of order encoding, original version from Constraints journal ppr. 
    private void orderEncodingLeqHelper2(Sat satModel, ArrayList<ASTNode> ch, long[] w, long leqValue, ArrayList<ArrayList<Intpair>> ranges, long[] tuple, int pos, long aux) throws IOException {
        if(pos==ch.size()) {
            long sum=0;
            for(int i=0; i<ch.size(); i++) {
                sum+=tuple[i];
            }
            
            if(sum == leqValue - ch.size()+1) {
                //  Generate a clause. 
                ArrayList<Long> clause=new ArrayList<Long>(ch.size());
                
                for(int i=0; i<ch.size(); i++) {
                    if(w[i]>0) {
                        long val=Divide.div(tuple[i], w[i]);
                        clause.add(ch.get(i).orderEncode(satModel, val));
                    }
                    else {
                        long val=Divide.divceil(tuple[i], w[i]);
                        clause.add(-ch.get(i).orderEncode(satModel, val-1));
                    }
                }
                System.out.println(clause);
                satModel.addClause(clause);
            }
        }
        else {
            ArrayList<Intpair> intervals=ranges.get(pos);
            for(long val=intervals.get(0).lower-1; val<=intervals.get(intervals.size()-1).upper; val++) {
                tuple[pos]=val;
                orderEncodingLeqHelper2(satModel, ch, w, leqValue, ranges, tuple, pos+1, aux);
            }
            
        }
    }
    
    public boolean usesSMTEncoding() {
        return CmdFlags.getUseBV() || CmdFlags.getUseNIA() || CmdFlags.getUseLIA() || (CmdFlags.getUseIDL() && canIDLEncode());
    }
    
    public boolean canIDLEncode() {
        if (weights.length == 2) {
            // Can only IDL encode if there are only two variables

            if (CmdFlags.getUseAuxSMT() && getChild(0) instanceof Identifier && getChild(1) instanceof Identifier)
                // If we can use auxiliary variables we can always encode if we have two identifiers
                return true;

            boolean ch0 = getChild(0) instanceof Identifier || getChild(0) instanceof NumberConstant
                    || getChild(0) instanceof SATLiteral || getChild(0) instanceof MultiplyMapper;
            boolean ch1 = getChild(1) instanceof Identifier || getChild(1) instanceof NumberConstant
                    || getChild(1) instanceof SATLiteral || getChild(1) instanceof MultiplyMapper;

            if (ch0 && ch1) {
                // If we cannot use auxiliary variables, we can only encode if the weights are right
                return (weights[0] == 1 && weights[1] == -1) || (weights[0] == -1 && weights[1] == 1);
            }
        }
        
        return false;
    }
    
    public String smtEncodeInt(SMT satModel) {
        if (CmdFlags.getUseNIA() || CmdFlags.getUseLIA()) {
            String s = "(+";

            ArrayList<ASTNode> children = getChildren();
            for (int i = 0; i < children.size(); i++) {
                ASTNode c = children.get(i);

                s += " (* " + SMT.toSMTInt(weights[i]) + " " + c.smtEncodeInt(satModel) + ")";
            }

            s += ")";

            return s;
        }
        else if (CmdFlags.getUseIDL() && canIDLEncode()) {
            String s = "(- ";

            String positive;
            String negative;

            try {
                // Here we try to reduce the number of auxiliary variables needed.
                // To do so, if we have one variable with a weight of 1 and another with a weight of -1, we do not
                // need any auxiliary variable.
                // Otherwise, if we have a 1 or a -1 we use that variable accordingly and we use an auxiliary variable
                // for the other part (if both weights are the same we will use the first one directly and an auxiliary
                // variable for the other one).
                // Finally, if none of those options is possible we will use an auxiliary variable for both variables.

                if (weights[0] == 1) {
                    positive = getChild(0).smtEncodeInt(satModel);

                    if (weights[1] == -1)
                        negative = getChild(1).smtEncodeInt(satModel);
                    else
                        negative = satModel.createAuxSMTVariableFor(getChild(1), -weights[1]);
                }
                else if (weights[0] == -1) {
                    negative = getChild(0).smtEncodeInt(satModel);

                    if (weights[1] == 1)
                        positive = getChild(1).smtEncodeInt(satModel);
                    else
                        positive = satModel.createAuxSMTVariableFor(getChild(1), weights[1]);
                }
                else if (weights[1] == 1) {
                    positive = getChild(1).smtEncodeInt(satModel);
                    negative = satModel.createAuxSMTVariableFor(getChild(0), -weights[0]);
                }
                else if (weights[1] == -1) {
                    negative = getChild(1).smtEncodeInt(satModel);
                    positive = satModel.createAuxSMTVariableFor(getChild(0), weights[0]);
                }
                else {
                    positive = satModel.createAuxSMTVariableFor(getChild(0), weights[0]);
                    negative = satModel.createAuxSMTVariableFor(getChild(1), -weights[1]);
                }

                s += positive + " " + negative;

                return s + ")";
            } catch (IOException e) {
                CmdFlags.errorExit("Could not create auxiliary variable for the node " + toString() + " because output file could not be accessed");
            }
        }

        return null;
    }

    public String smtEncodeBV(SMT satModel) {
        if (CmdFlags.getUseBV()) {
            StringBuilder s=new StringBuilder();
            if(numChildren()>1) {
                s.append("(bvadd");
            }
            
            //bvadd has fixed arity of two so will probably need to change later
            
            for (int i = 0; i < numChildren(); i++) {
                if (weights[i] == 1) {
                    s.append(" ");
                    s.append(getChild(i).smtEncodeBV(satModel));
                }
                else if (weights[i] == -1) {
                    s.append(" (bvneg ");
                    s.append(getChild(i).smtEncodeBV(satModel));
                    s.append(")");
                }
                else {
                    s.append(" (bvmul ");
                    s.append(SMT.toSMTBV(weights[i]));
                    s.append(" ");
                    s.append(getChild(i).smtEncodeBV(satModel));
                    s.append(")");
                }
            }
            
            if(numChildren()>1) {
                s.append(")");
            }
            
            return s.toString();
        }
        return null;
    }

    public void toSATLeq(Sat satModel, long leqValue) throws IOException {
        //  Assumes we have  sum <= constant.
        long[] w=new long[numChildren()];
        boolean allone=true;
        boolean allbool=true;
        for(int i=0; i<numChildren(); i++) {
            w[i]=weights[i];
            if(w[i]!=1) allone=false;
            if(!getChild(i).isRelation()) allbool=false;
        }
        
        if(CmdFlags.sat_amo_encoding== AMOEnc.COMMANDER && allone && allbool && leqValue==1) {
            satModel.commanderEncodingAMO(getChildren(), false);
        }
        else if(CmdFlags.sat_amo_encoding==AMOEnc.PRODUCT && allone && allbool && leqValue==1) {
            satModel.productEncodingAMO(getChildren(), false);
        }
        else if(CmdFlags.sat_amo_encoding==AMOEnc.LADDER && allone && allbool && leqValue==1) {
            satModel.ladderEncodingAMO(getChildren(), false);
        }
        else if(CmdFlags.sat_amo_encoding==AMOEnc.PAIRWISE && allone && allbool && leqValue==1) {
            satModel.AMOBinomial(getChildren(), false);
        }
        else if(CmdFlags.sat_amo_encoding==AMOEnc.BIMANDER && allone && allbool && leqValue==1) {
            satModel.bimanderEncodingAMO(getChildren(), false);
        }
        else {
            orderEncodingLeq(satModel, w, leqValue, 0);
        }
    }
    
    public void toSATGeq(Sat satModel, long geqValue) throws IOException {
        // We have  sum >= constant. Negate all weights and the constant to make -sum <= -constant.
        long[] w=new long[numChildren()];
        for(int i=0; i<numChildren(); i++) w[i]=-weights[i];
        
        orderEncodingLeq(satModel, w, -geqValue, 0);
    }
    
    public void toSATLeqWithAuxVar(Sat satModel, long leqValue, long aux) throws IOException {
        // First, generate aux ->   this<=leqvalue.
        long[] w=new long[numChildren()];
        for(int i=0; i<numChildren(); i++) w[i]=weights[i];
        
        orderEncodingLeq(satModel, w, leqValue, -aux);   //  Adds -aux to all clauses.
        
        // Second, generate -aux ->  this>=leqvalue+1
        for(int i=0; i<numChildren(); i++) w[i]=-weights[i];
        
        orderEncodingLeq(satModel, w, -(leqValue+1), aux);   //  Adds aux to all clauses.
    }

    public void toSATGeqWithAuxVar(Sat satModel, long geqValue, long aux) throws IOException {
        // First, generate aux ->   this>=geqvalue.
        long[] w=new long[numChildren()];
        for(int i=0; i<numChildren(); i++) w[i]=-weights[i];
        
        orderEncodingLeq(satModel, w, -geqValue, -aux);   //  Adds -aux to all clauses.
        
        // Second, generate -aux ->  this<=geqvalue-1
        for(int i=0; i<numChildren(); i++) w[i]=weights[i];
        
        orderEncodingLeq(satModel, w, geqValue-1, aux);   //  Adds aux to all clauses.
    }
    
    //////////////////////////////////////////////////////////////////////////
    //  MIP output
    
    public void toMIP(BufferedWriter b) throws IOException {
        for(int i=0; i<numChildren(); i++) {
            if(weights[i]<0) {
                b.append(" - ");
                b.append(String.valueOf(-weights[i]));
            }
            else if(weights[i]>0) {
                if(i>0) {
                    b.append(" + ");
                }
                b.append(String.valueOf(weights[i]));
            }
            b.append(" ");
            b.append(getChild(i).toString());
        }
    }
    
	////////////////////////////////////////////////////////////////////////////
	// SAT encoding -- Only used for EO Boolean sum. 
	
    public void toSATWithAuxVar(Sat satModel, ASTNode auxVar) throws IOException {
        assert Sat.eligibleAMO(this) && auxVar.isConstant() && auxVar.getValue()==1;
        if(CmdFlags.sat_amo_encoding==AMOEnc.COMMANDER) {
            satModel.commanderEncodingAMO(getChildren(), true); //  exactly-one by commander.
        }
        else if(CmdFlags.sat_amo_encoding==AMOEnc.PRODUCT) {
            satModel.productEncodingAMO(getChildren(), true); //  exactly-one by product.
        }
        else if(CmdFlags.sat_amo_encoding==AMOEnc.LADDER) {
            satModel.ladderEncodingAMO(getChildren(), true); //  exactly-one by ladder.
        }
        else if(CmdFlags.sat_amo_encoding==AMOEnc.PAIRWISE) {
            satModel.AMOBinomial(getChildren(), true);
        }
        else if(CmdFlags.sat_amo_encoding==AMOEnc.BIMANDER) {
            satModel.bimanderEncodingAMO(getChildren(), true);   //  Exactly-one by bimander. 
        }
        else {
            CmdFlags.errorExit("Unknown SAT encoding for AMO/EO constraints.");
        }
    }
    
    public boolean test(long val1, long val2, long aux) {
        return func(val1, val2)==aux;
    }
    public long func(long val1, long val2) {
        return weights[0]*val1 + weights[1]*val2;
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //  Symmetry
    
    public void toJSON(StringBuilder bf) {
        if (getParent() != null && getParent().canChildBeConvertedToDifference(getChildNo()) && isValidDifference()) {
            toJSONAsDifference(bf);
            return;
        }
        toJSONHeader(bf, true);
        bf.append("\"children\": [");
        for (int i = 0; i < numChildren(); i++) {
            bf.append("\n");
            // make times object out of weight and variable/constant
            // first convert weight to constant node type
            NumberConstant nc = NumberConstant.make(weights[i]);
            Times tempTimes = new Times(nc, getChild(i));
            tempTimes.toJSON(bf);
            bf.append(",");
        }
        bf.append("]\n}");
    }
    
    public boolean childrenAreSymmetric() {
        return true;
    }
    
    /**
     * Checks if this sum consists of weights of the same magnitude   
     * @return true if the above cases are matched
     */
    public boolean isValidDifference() {
        long firstWeight = Math.abs(weights[0]);
        for (int i = 1; i < numChildren(); i++) {
            if (firstWeight != Math.abs(weights[i]))
                return false;
        }
        return true;
    }
    
    public void toJSONAsDifference(StringBuilder bf) {
        String json = "{\n\"type\": \"Difference\",\n\"symmetricChildren\": true,\n\"children\": [";
        ArrayList<ASTNode> tempNodes = collectNodesOfSign(true); //collect positive 
        ArrayList<Long> tempWeights = makeFilledList(tempNodes.size(), Math.abs(weights[0]));
        WeightedSum leftSum = new WeightedSum(tempNodes, tempWeights);
        tempNodes = collectNodesOfSign(false); //collect  nodesnegative
        tempWeights = makeFilledList(tempNodes.size(), Math.abs(weights[0]));
        WeightedSum rightSum = new WeightedSum(tempNodes, tempWeights);
        
        bf.append(json);
        
        bf.append("\n");
        leftSum.toJSON(bf);
        bf.append(",\n");
        rightSum.toJSON(bf);
        bf.append("]\n}");
    }
    
    public ArrayList<ASTNode> collectNodesOfSign(boolean positive) {
        ArrayList<ASTNode> nodes = new ArrayList<ASTNode>();
        for (int i = 0; i < numChildren(); i++) {
            if ((positive && weights[i] > 0) || (!positive && weights[i] < 0))
                nodes.add(getChild(i));
        }
        return nodes;
    }
    
    public ArrayList<Long> makeFilledList(int size, long value) {
        ArrayList<Long> longs = new ArrayList<Long>();
        for (int i = 0; i < size; i++) {
            longs.add(value);
        }
        return longs;
    }
}
