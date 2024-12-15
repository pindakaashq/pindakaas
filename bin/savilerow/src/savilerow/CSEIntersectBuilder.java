package savilerow; 

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Hashtable;
import java.util.Map;

// Build a hashtable of lists of terms to the sums they are in
public class CSEIntersectBuilder<T extends Comparable<T>> {

  // For each occurance of the AC operator, give a list of the children of the operator
  public CSEIntersectBuilder(ArrayList<ArrayList<T>> entries) {
    cse = new Hashtable<ArrayList<T>,ArrayList<Integer>>(entries.size(),0.75f);

    added = new ArrayList<Map.Entry<ArrayList<T>,ArrayList<Integer>>>(entries.size());

    for(int i = 0;i < entries.size(); ++i) {
      added.add(new AbstractMap.SimpleEntry<ArrayList<T>,ArrayList<Integer>>(mkMSet(entries.get(i))
                                                                            ,new ArrayList<Integer>(Arrays.asList(i))));
    }
  }

  // Iterate the intersection step. Return true if something happened, otherwise false and all intersections are found.
  public boolean iterate() {
    ArrayList<Map.Entry<ArrayList<T>,ArrayList<Integer>>> a = new ArrayList<Map.Entry<ArrayList<T>,ArrayList<Integer>>>();

    boolean r = false;
    for (int i = 0;i < added.size();++i) {
      for (int j = i+1;j < added.size();++j) {
        Map.Entry<ArrayList<T>,ArrayList<Integer>> r0 = addItem(added.get(i),added.get(j));
        if(r0 != null) {
          a.add(r0);
          r = true;
        }
      }
    }
    added = a;
    return r;
  }

  // get all the cses found so far
  public Hashtable<ArrayList<T>,ArrayList<Integer>> getCSE() {
    return cse;
  }

  // The cse, and the index of the things they occur in
  private Hashtable<ArrayList<T>,ArrayList<Integer>> cse;
  // The cse's added in the last iteration need to be intersected with each other
  private ArrayList<Map.Entry<ArrayList<T>,ArrayList<Integer>>> added;

  // Add the intersection of the two entries to the hash map
  // Returns the item added, or null if nothing was added
  private Map.Entry<ArrayList<T>,ArrayList<Integer>> addItem(Map.Entry<ArrayList<T>,ArrayList<Integer>> xe,Map.Entry<ArrayList<T>,ArrayList<Integer>> ye) {
    // get the intersection of the keys (common terms)
    ArrayList<T> x = xe.getKey();
    ArrayList<T> y = ye.getKey();
    ArrayList<T> z = msetIntersect(x,y);
    // Nothing in the intersection, or intersection is size one
    if (z.size() < 2)
      return null;

    ArrayList<Integer> e = cse.get(z);
    ArrayList<Integer> n = setUnion(xe.getValue(),ye.getValue());
    // The intersection of keys is not in the hash map, add it
    if (e == null) {
      cse.put(z,n);
      return new AbstractMap.SimpleEntry<ArrayList<T>,ArrayList<Integer>>(z,n);
    }

    // Check the intersection of values for the new key is changed
    if (e.equals(n)) {
      return null;
    }

    // Otherwise add the new stuff into the map
    cse.put(z,setUnion(e,n));
    return new AbstractMap.SimpleEntry<ArrayList<T>,ArrayList<Integer>>(z,setUnion(e,n));
  }

  // sort the list 
  private <U extends Comparable<U>> ArrayList<U> mkMSet(ArrayList<U> in) {
    ArrayList<U> out = new ArrayList<U>(in);
    Collections.sort(out);
    return out;
  }

  // take a union of two sorted and duplicate free lists
  private <U extends Comparable<U>> ArrayList<U> setUnion(ArrayList<U> x,ArrayList<U> y) {
    ArrayList<U> z = new ArrayList<U>();
    int i=0, j=0;
    while (i < x.size() && j < y.size()) {
      int cmp = x.get(i).compareTo(y.get(j));
      if (cmp == 0) {
        z.add(x.get(i));
        ++i;++j;
      } else if (x.get(i).compareTo(y.get(j)) < 0) {
        z.add(x.get(i));
        ++i;
      } else {
        z.add(y.get(j));
        ++j;
      }
    }
    if (i < x.size()) 
      z.addAll(x.subList(i,x.size()));
    if (j < y.size()) 
      z.addAll(y.subList(j,y.size()));
    
    return z;
  }

  // take an intersection of two sorted lists
  <U extends Comparable<U>> ArrayList<U> msetIntersect(ArrayList<U> x,ArrayList<U> y) {
    ArrayList<U> z = new ArrayList<U>();
    int i=0, j=0;
    while (i < x.size() && j < y.size()) {
      int cmp = x.get(i).compareTo(y.get(j));
      if (cmp == 0) {
        z.add(x.get(i));
        ++i;++j;
      } else if (cmp < 0) {
        ++i;
      } else {
        ++j;
      }
    }
    
    return z;
  }

  public static void main(String[] args) {
    ArrayList<Character> e0 = new ArrayList<Character>(Arrays.asList('x','y','z','a'));
    ArrayList<Character> e1 = new ArrayList<Character>(Arrays.asList('x','y','z','b','x','x'));
    ArrayList<Character> e2 = new ArrayList<Character>(Arrays.asList('x','y','w','a','b','x','y'));

    ArrayList<ArrayList<Character>> es = new ArrayList<ArrayList<Character>>(Arrays.asList(e0,e1,e2));

    CSEIntersectBuilder<Character> cse = new CSEIntersectBuilder<Character>(es);

    System.out.println(es);

    while (cse.iterate()) {
      System.out.println(cse.getCSE());
    }
  }
}
