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






import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

import savilerow.CmdFlags;
import savilerow.expression.*;
import savilerow.treetransformer.*;

//  If extended domain filtering is switched on, store domains in here.
//  The main methods are guarded by the extended domain filtering switch. 

public class FilteredDomainStore {
    private static final long serialVersionUID = 1L;
    
    //  Data to implement filtered aux domains
    //  Maps from aux variable name to the expression that it represented /when it was introduced/.
    private HashMap<String, ASTNode> aux_to_expression;
    
    //  Maps from expression to filtered domain.
    private HashMap<ASTNode, ASTNode> aux_filtered_domain;
    
    SymbolTable st;
    
    // Track where we are in the process by which methods are being called. Crude. 
    private boolean firstPass;
    private boolean storeDomains;   
    
    public FilteredDomainStore(SymbolTable _st) {
        st=_st;
        
        aux_to_expression=new HashMap<String, ASTNode>();
        aux_filtered_domain=new HashMap<ASTNode, ASTNode>();
        
        firstPass=true;   // Once filtered domains are stored, this flips to false.
        storeDomains=false;
    }
    
    @Override
    public boolean equals(Object b) {
        if (! (b instanceof FilteredDomainStore)) {
            return false;
        }
        FilteredDomainStore c = (FilteredDomainStore) b;
        if (! c.aux_to_expression.equals(aux_to_expression)) {
            return false;
        }
        if (! c.aux_filtered_domain.equals(aux_filtered_domain)) {
            return false;
        }
        if( (c.firstPass != firstPass) || (c.storeDomains != storeDomains) ) {
            return false;
        }
        return true;
    }
    
    @Override
    public int hashCode() {
        return Objects.hash(aux_to_expression, aux_filtered_domain, firstPass, storeDomains);
    }
    
    public FilteredDomainStore copy(SymbolTable _st) {
        FilteredDomainStore f=new FilteredDomainStore(_st);
        TransformFixSTRef tf = new TransformFixSTRef(_st.m);
        
        for (String auxst : aux_to_expression.keySet()) {
            f.aux_to_expression.put(auxst, tf.transform(aux_to_expression.get(auxst).copy()));
        }
        for (ASTNode auxct : aux_filtered_domain.keySet()) {
            f.aux_filtered_domain.put(tf.transform(auxct.copy()), tf.transform(aux_filtered_domain.get(auxct).copy()));
        }
        f.firstPass=firstPass;
        f.storeDomains=storeDomains;
        return f;
    }
    
    //   Need to simplify domains when they are not 
    //   associated to an aux variable....
    //   Prob. need to only simplify during second tailoring process.
    //   Perhaps only simplify aux_filtered_domain.   ??
    
    //   Need to intersect two domains if the expressions linked to them become equal.
    
    public void simplify() {
        if(CmdFlags.getUsePropagateExtend() && !firstPass) {
            TransformSimplify ts=new TransformSimplify();
            TransformNormalise tn=new TransformNormalise(st.m);
            
            // Replace the aux_filtered_domain hashtable.
            HashMap<ASTNode, ASTNode> repl=new HashMap<ASTNode, ASTNode>(aux_filtered_domain.size(), (float)0.75);
            
            for (Map.Entry<ASTNode, ASTNode> entry : aux_filtered_domain.entrySet()) {
                ASTNode exp = entry.getKey();
                ASTNode dom = entry.getValue();
                
                ASTNode expsimp = ts.transform(exp.copy());
                
                if(! expsimp.equals(exp)) {
                    expsimp=tn.transform(expsimp);   // normalise AC expressions.
                    
                    // exp has changed, it may now collide with another entry.
                    if(repl.containsKey(expsimp)) {
                        //  Replace the two entries with one containing the intersection of the two domains.
                        repl.put(expsimp, ts.transform(new Intersect(repl.get(expsimp), dom)));
                    }
                    else {
                        repl.put(expsimp, dom);
                    }
                }
                else {
                    //  No change by simplification -- just copy the old entry.
                    
                    // Another entry may have changed key, so check for collision.
                    if(repl.containsKey(exp)) {
                        //  Replace the two entries with one containing the intersection of the two domains.
                        repl.put(exp, ts.transform(new Intersect(repl.get(exp), dom)));
                    }
                    else {
                        repl.put(exp, dom);
                    }
                }
            }
            
            aux_filtered_domain=repl;  //  Replace the hashtable. 
        }
    }
    
    //  Methods to store data for aux filtering.
    public void auxVarRepresentsAST(String name, ASTNode exp) {
        if(CmdFlags.getUsePropagateExtend()) {
            if(!firstPass && storeDomains) {
                // Starting second pass -- clear out the auxiliary variables from the first pass. 
                aux_to_expression.clear();
                storeDomains=false;
            }
            
            TransformDeAux tda=new TransformDeAux(aux_to_expression);
            TransformSimplify ts=new TransformSimplify();
            TransformNormalise tn=new TransformNormalise(st.m);
            
            ASTNode expcp=exp.copy();
            expcp=tda.transform(expcp);
            expcp=ts.transform(expcp);    //  Simplify
            expcp=tn.transform(expcp);    //  Normalise
            
            if(! expcp.containsAux()) {
                // some aux vars are not representing an expression. So unfortunately not all can be eliminated.
                //expression_to_aux.put(expcp, name);
                aux_to_expression.put(name, expcp);
            }
        }
    }
    
    public void auxVarFilteredDomain(String name, ASTNode dom) {
        if(CmdFlags.getUsePropagateExtend()) {
            // Look up the deauxed expression and use it as the key to store the domain. 
            ASTNode expression=aux_to_expression.get(name);
            if(expression!=null) {
                //  Some aux variables represent no expression. Must test for null. 
                aux_filtered_domain.put(expression.copy(), dom);   // Take a copy of the key to avoid any changes from elsewhere.
            }
            
            firstPass=false;   //  As soon as domains are stored, we must have finished the first pass.
            storeDomains=true;
        }
    }
    
    //  Construct a domain for an aux var using the storage.
    public ASTNode constructDomain(ASTNode exp, ASTNode dom) {
        if(!firstPass && storeDomains) {
            // Starting second pass -- clear out the auxiliary variables from the first pass. 
            aux_to_expression.clear();
            storeDomains=false;
        }
        
        // If we are on the first pass, no point looking up domain in aux_filtered_domain -- hash table should be empty. 
        if((!firstPass) && CmdFlags.getUsePropagateExtend()) {
            TransformDeAux tda=new TransformDeAux(aux_to_expression);
            TransformSimplify ts=new TransformSimplify();
            TransformNormalise tn=new TransformNormalise(st.m);
            
            ASTNode expcp=exp.copy();
            expcp=tda.transform(expcp);
            expcp=ts.transform(expcp);    //  Simplify
            expcp=tn.transform(expcp);    //  Normalise
            
            //System.out.println("In constructDomain expression with aux:"+exp+"   expression without aux:"+expcp);
            
            ASTNode filtdom=aux_filtered_domain.get(expcp);
            
            if(filtdom!=null) {
                filtdom = new Intersect(filtdom, dom);
                // Intersect correctly casts a boolean set to a non-boolean set when
                // intersecting it with a set of int. Sort out the boolean case.
                // This is a rather unpleasant hack.
                if (dom.isBooleanSet()) {
                    filtdom = Intpair.makeDomain((ts.transform(filtdom)).getIntervalSet(), true);
                }
                filtdom=ts.transform(filtdom);
                
                return filtdom;
            }
        }
        return dom;
    }
    
    //  Construct a domain for an aux var using the storage.
    public ASTNode constructDomain(ASTNode exp, long lb, long ub) {
        if(lb==0 && ub==1) {
            return constructDomain(exp, new BooleanDomainFull());
        }
        else {
            return constructDomain(exp, new IntegerDomain(new Range(NumberConstant.make(lb), NumberConstant.make(ub))));
        }
    }
    
    // For debugging
    public String toString() {
        StringBuilder b=new StringBuilder();
        b.append("FilteredDomainStore:\n");
        b.append("Mapping from aux to expression:\n");
        b.append(aux_to_expression.toString());
        b.append("From expression to filtered domain:\n");
        b.append(aux_filtered_domain.toString());
        return b.toString();
    }
}
