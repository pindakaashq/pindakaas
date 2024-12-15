package savilerow.treetransformer;
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





import java.util.ArrayList;

import savilerow.CmdFlags;
import savilerow.expression.*;
import savilerow.model.Model;

public class TransformEOPB extends TreeTransformerBottomUpNoWrapper
{
    public TransformEOPB(Model _m, boolean _prop) {
        super(_m);
        propagate=_prop;
    }
    
    boolean propagate;
    
    protected NodeReplacement processNode(ASTNode curnode)
	{
	    if(curnode instanceof EOPB)
        {
            assert curnode.getChild(0).isMatrixLiteral() && curnode.getChild(1).isConstant();
            
            if(CmdFlags.getSattrans() && !propagate) {
                // Convert to AMOPB with introduction of some new Boolean variables and
                // implications. 
                ArrayList<ASTNode> ch = curnode.getChild(0).getChildren(1);
                
                ArrayList<ASTNode> conj=new ArrayList<>();
                long k=curnode.getChild(1).getValue();
                
                for(int i=0; i<ch.size(); i++) {
                    ASTNode coeffs_group=ch.get(i).getChild(1);
                    ASTNode bools_group=ch.get(i).getChild(2);
                    
                    assert coeffs_group.getCategory()==ASTNode.Constant;
                }
                
                for(int i=0; i<ch.size(); i++) {
                    ArrayList<ASTNode> coeffs_group=ch.get(i).getChild(1).getChildren(1);
                    ArrayList<ASTNode> bools_group=ch.get(i).getChild(2).getChildren(1);
                    assert coeffs_group.size()==bools_group.size();
                    
                    // Sort by coeffs.
                    for(int j=0; j<coeffs_group.size(); j++) {
                        for(int l=j+1; l<coeffs_group.size(); l++) {
                            if(coeffs_group.get(j).getValue()>coeffs_group.get(l).getValue()) {
                                ASTNode swap=coeffs_group.get(j);
                                coeffs_group.set(j, coeffs_group.get(l));
                                coeffs_group.set(l, swap);
                                
                                swap=bools_group.get(j);
                                bools_group.set(j, bools_group.get(l));
                                bools_group.set(l, swap);
                            }
                        }
                    }
                    
                    ArrayList<Long> coeffs=new ArrayList<Long>();
                    for(int j=0; j<coeffs_group.size(); j++) {
                        coeffs.add(coeffs_group.get(j).getValue());
                    }
                    //System.out.println("Full EO group: "+coeffs_group+", "+bools_group+", k="+k);
                    // Take out the smallest element(s) and update k. 
                    long smallcoeff=coeffs.get(0);
                    k=k-smallcoeff;
                    
                    ArrayList<ASTNode> disj=new ArrayList<ASTNode>();  // disjunction of removed terms. 
                    for(int j=0; j<coeffs_group.size(); j++) {
                        if(coeffs.get(j)==smallcoeff) {
                            disj.add(new Negate(bools_group.remove(j)));
                            coeffs_group.remove(j);
                            coeffs.remove(j);
                            j--;
                        }
                        else {
                            coeffs_group.set(j, NumberConstant.make(coeffs.get(j)-smallcoeff));
                            coeffs.set(j, coeffs.get(j)-smallcoeff);
                        }
                    }
                    
                    //System.out.println("AMO group: "+coeffs_group+", "+bools_group);
                    
                    //  Deduplicate as well as adding the implication chain. 
                    
                    // smallest term(s) all false imply one of the next smallest, etc.
                    //  Don't do the last one; avoid making one variable etc.  Last one should be set by EO constraint.
                    for(int j=0; j<coeffs_group.size()-1; j++) {
                        ASTNode locvar=m.global_symbols.newAuxiliaryVariable(0,1);
                        
                        ArrayList<ASTNode> origvars=new ArrayList<ASTNode>();
                        
                        //  Replace var at position j.
                        ASTNode original_var=bools_group.get(j);
                        bools_group.set(j, locvar);
                        
                        origvars.add(original_var);
                        conj.add(new Implies(original_var, locvar));  //  original x implies the new variable.
                        
                        //  Replace any others from j+1 that have same coeff. 
                        while(j+1<coeffs_group.size() && coeffs.get(j+1)==coeffs.get(j)) {
                            origvars.add(bools_group.get(j+1));
                            
                            conj.add(new Implies(bools_group.get(j+1), locvar));
                            
                            //  Remove the duplicate coeff term. 
                            bools_group.remove(j+1);
                            coeffs_group.remove(j+1);
                            coeffs.remove(j+1);
                        }
                        
                        if(j<coeffs_group.size()-1) {
                            //  Don't do the last one, it should be set by EO constraint. 
                            ASTNode newct=new Implies(new And(disj), locvar);
                            //System.out.println("Adding constraint: "+newct);
                            conj.add(newct);   //  Implication -- neg of all smaller terms false causes locvar to become true.
                        }
                        
                        //  Add origvars to disj for next iteration. 
                        for(int z=0; z<origvars.size(); z++) {
                            disj.add(new Negate(origvars.get(z)));
                        }
                    }
                    //System.out.println("AMO group: "+coeffs_group+", "+bools_group+", k="+k);
                    
                    assert coeffs_group.size()==bools_group.size();
                    ASTNode cg=CompoundMatrix.make(coeffs_group);
                    ASTNode bg=CompoundMatrix.make(bools_group);
                    ch.set(i, CompoundMatrix.make(cg, bg));
                }
                
                ASTNode amopb=new AMOPB(CompoundMatrix.make(ch), NumberConstant.make(k), curnode.getChild(2), ((EOPB)curnode).fromPB);
                conj.add(amopb);  //  Add into conjunction with implied constraints etc
                return new NodeReplacement(new And(conj));
            }
            else {
                // Convert for backends other than SAT/MaxSAT/SMT. Just make it an AMOPB.
                return new NodeReplacement(new AMOPB(curnode.getChild(0), curnode.getChild(1), curnode.getChild(2), ((EOPB)curnode).fromPB));
            }
        }
        return null;
    }
}
