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
import java.util.Arrays;

// Abstract Syntax Tree node with children.

public abstract class ASTNodeC extends ASTNode {
    public static final long serialVersionUID = 1L;
    
    private ASTNode[] children;
    
    int hashCache;    //  Integer.MIN_VALUE means no cached value.
    
    /* ====================================================================
     constructor
    ==================================================================== */
    ASTNodeC() {
        children = null;
        hashCache=Integer.MIN_VALUE;
    }
    
    ASTNodeC(ASTNode a) {
        children = new ASTNode[1];
        if (a.getParent() == null) {
            children[0] = a;
        } else {
            children[0] = a.copy();
        }
        children[0].setParent(this);
        children[0].childno = 0;
        
        hashCache=Integer.MIN_VALUE;
    }
    
    ASTNodeC(ASTNode a, ASTNode b) {
        children = new ASTNode[2];

        if (a.getParent() == null) {
            children[0] = a;
        } else {
            children[0] = a.copy();
        }
        children[0].setParent(this);
        children[0].childno = 0;

        if (b.getParent() == null) {
            children[1] = b;
        } else {
            children[1] = b.copy();
        }
        children[1].setParent(this);
        children[1].childno = 1;
        
        hashCache=Integer.MIN_VALUE;
    }
    
    ASTNodeC(ASTNode a, ASTNode b, ASTNode c) {
        ASTNode[] ch = new ASTNode[3];
        ch[0]=a;
        ch[1]=b;
        ch[2]=c;
        
        for(int i=0; i<3; i++) {
            if(ch[i].getParent()!=null) {
                ch[i]=ch[i].copy();
            }
            
            ch[i].setParent(this);
            ch[i].childno = i;
        }
        children=ch;
        
        hashCache=Integer.MIN_VALUE;
    }
    
    ASTNodeC(ASTNode a, ASTNode b, ASTNode c, ASTNode d) {
        ASTNode[] ch = new ASTNode[4];
        ch[0]=a;
        ch[1]=b;
        ch[2]=c;
        ch[3]=d;
        
        for(int i=0; i<4; i++) {
            if(ch[i].getParent()!=null) {
                ch[i]=ch[i].copy();
            }
            
            ch[i].setParent(this);
            ch[i].childno = i;
        }
        children=ch;
        
        hashCache=Integer.MIN_VALUE;
    }
    
    ASTNodeC(ASTNode[] ch) {
        for(int i=0; i<ch.length; i++) {
            if(ch[i].getParent()!=null) {
                ch[i]=ch[i].copy();
            }
            
            ch[i].setParent(this);
            ch[i].childno = i;
        }
        children=ch;
        
        hashCache=Integer.MIN_VALUE;
    }
    
    ASTNodeC(ASTNode a, ASTNode[] chin) {
        ASTNode[] ch=new ASTNode[1+chin.length];
        ch[0]=a;
        for(int i=0; i<chin.length; i++) {
            ch[i+1]=chin[i];
        }
        
        for(int i=0; i<ch.length; i++) {
            if(ch[i].getParent()!=null) {
                ch[i]=ch[i].copy();
            }
            
            ch[i].setParent(this);
            ch[i].childno = i;
        }
        children=ch;
        
        hashCache=Integer.MIN_VALUE;
    }
    
    // Special stop-gap constructor, should not be used in new classes. 
    ASTNodeC(ArrayList<ASTNode> chin) {
        ASTNode[] ch=new ASTNode[chin.size()];
        for(int i=0; i<ch.length; i++) {
            ch[i]=chin.get(i);
            if(ch[i].getParent()!=null) {
                ch[i]=ch[i].copy();
            }
            
            ch[i].setParent(this);
            ch[i].childno = i;
        }
        children=ch;
        
        hashCache=Integer.MIN_VALUE;
    }
    
    /* ====================================================================
     getChildren
    ==================================================================== */
    public final ArrayList<ASTNode> getChildren() {
        return children == null ? new ArrayList<ASTNode>() : new ArrayList<ASTNode>(Arrays.asList(children));
    }
    
    public final ArrayList<ASTNode> getChildren(int first) {
        if(children==null) return new ArrayList<ASTNode>();
        // Copy from first to the end.
        ArrayList<ASTNode> ret=new ArrayList<ASTNode>(children.length-first);
        for(int i=first; i<children.length; i++) {
            ret.add(children[i]);
        }
        return ret;
    }
    
    public final ASTNode[] getChildrenArray() {
        if(children==null) return null;
        ASTNode[] ch = new ASTNode[children.length];
        System.arraycopy(children, 0, ch, 0, children.length );
        return ch;
    }
    
    public final ASTNode[] getChildrenArray(int startpos) {
        if(children==null) return null;
        ASTNode[] ch = new ASTNode[children.length-startpos];
        System.arraycopy(children, startpos, ch, 0, children.length-startpos );
        return ch;
    }
    
    /* ====================================================================
     setChildren  --  these should be removed eventually. 
    ==================================================================== */
    public final void setChildren(ASTNode[] ch) {
        for(int i=0; i<ch.length; i++) {
            if(ch[i].getParent()!=null) {
                ch[i]=ch[i].copy();
            }
            
            ch[i].setParent(this);
            ch[i].childno = i;
        }
        children=ch;
    }
    
    public final void setChildren(ArrayList<ASTNode> ch) {
        setChildren(ch.toArray(new ASTNode[ch.size()]));
    }
    
    /* ====================================================================
     Get and set individual children -- must be used instead of accessing
     the 'children' array directly.
    ==================================================================== */

    public final void setChild(int i, ASTNode c) {
        if (c == null) {
            children[i] = null;
        } else {
            if (c.getParent() == null) {
                // If c has no parent, assume we do not need to copy it.
                children[i] = c;
                c.setParent(this);
                c.childno = i;
            } else {
                children[i] = c.copy();
                children[i].setParent(this);
                children[i].childno = i;
            }
        }
        
        // Reset hashCache values 
        ASTNode p=this;
        while(p!=null) {
            if(p instanceof ASTNodeC) {
                ((ASTNodeC)p).hashCache=Integer.MIN_VALUE;
            }
            p=p.getParent();
        }
    }
    
    public final ASTNode getChild(int i) {
        return children[i];
    }
    
    //  Same as above with a promise the caller will not make internal changes
    //  in the AST that is returned. Derefs constant matrices. 
    public ASTNode getChildConst(int i) {
        if(children[i] instanceof Identifier) {
            return ((Identifier)children[i]).getCM();
        }
        else {
            return children[i];
        }
    }
    
    //  Avoid children of this ASTNode being copied when this ASTNode is replaced. 
    public final void detachChildren() {
        if(children!=null) {
            for(int i=0; i<children.length; i++) {
                children[i].parent=null;
            }
        }
    }
    
    public String toString() {
        String st = getClass().getName();
        st = st.substring(st.lastIndexOf('.') + 1);        // chop off package name
        st = st + "(";
        if (children == null) {
            st = st + "NULL-POINTER";
        } else {
            for (int i =0; i < numChildren(); i++) {
                st = st + getChild(i);
                if (i < numChildren() - 1) {
                    st = st + ", ";
                }
            }
        }
        return st + ")";
    }

    public String generic_to_string(String name) {
        String st = name + "(";
        if (children == null) {
            st = st + "NULL-POINTER";
        } else {
            for (int i =0; i < numChildren(); i++) {
                st = st + getChild(i);
                if (i < numChildren() - 1) {
                    st = st + ", ";
                }
            }
        }
        return st + ")";
    }

    public int numChildren() { return (children == null) ? 0 : children.length; }
    
    @Override
    public int hashCode() {
        if(hashCache==Integer.MIN_VALUE) {
            hashCache = (this.getClass().getName()).hashCode() * 13 + Arrays.hashCode(children);
        }
        return hashCache;
    }
    
    /* ====================================================================
     equals()
     Deep equality.
     Must be overridden by any subclass that has its own internal state.
     For example, NumberConstant.
    ==================================================================== */
    @Override
    public boolean equals(Object b) {
        if (this.getClass() != b.getClass()) {
            return false;
        }
        ASTNode b2=(ASTNode)b;
        if (numChildren() != b2.numChildren()) {
            return false;
        }
        for (int i = 0; i < numChildren(); i++) {
            if (! getChild(i).equals(b2.getChild(i))) {
                return false;
            }
        }
        return true;
    }
    
    //  In-place version that uses Java's Arrays.sort.
    //  Assumes the normalise tranversals are in bottom-up order. 
    public boolean normaliseInPlace() {
        boolean changed=false;
        //  Is it out of order?
        for (int i =0; i < children.length-1; i++) {
            if(children[i].hashCode()>children[i+1].hashCode()) {
                changed=true;
                break;
            }
        }
        
        if(!changed) {
            return false;
        }
        
        Arrays.sort(children, new cmphash());
        for(int i=0; i<children.length; i++) {
            children[i].childno=i;
        }
        // Reset hashCache values up to root.  
        ASTNode p=this;
        while(p!=null) {
            if(p instanceof ASTNodeC) {
                ((ASTNodeC)p).hashCache=Integer.MIN_VALUE;
            }
            p=p.getParent();
        }
        
        return true;
    }
    
    //  In-place version that uses Java's Arrays.sort.
    //  Assumes the normalise tranversals are in bottom-up order. 
    public boolean normaliseInPlaceAlpha() {
        boolean changed=false;
        //  Is it out of order?
        for (int i =0; i < children.length-1; i++) {
            if(children[i].toString().compareTo(children[i+1].toString())>0) {
                changed=true;
                break;
            }
        }
        
        if(!changed) {
            return false;
        }
        
        Arrays.sort(children, new cmpstring());
        for(int i=0; i<children.length; i++) {
            children[i].childno=i;
        }
        // Reset hashCache values up to root.  
        ASTNode p=this;
        while(p!=null) {
            if(p instanceof ASTNodeC) {
                ((ASTNodeC)p).hashCache=Integer.MIN_VALUE;
            }
            p=p.getParent();
        }
        
        return true;
    }
}
