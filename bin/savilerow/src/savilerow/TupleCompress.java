package savilerow;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2016 Chris Jefferson

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
import java.util.HashSet;

import savilerow.expression.Intpair;

public class TupleCompress {

	public static class TupleReturn
	{
		public HashSet<ArrayList<Long>> squashed_tuples;
		public HashSet<ArrayList<Long>> unsquashed_tuples;

		public TupleReturn(HashSet<ArrayList<Long>> _squashed_tuples,
								       HashSet<ArrayList<Long>> _unsquashed_tuples)
		{
			squashed_tuples = _squashed_tuples;
			unsquashed_tuples = _unsquashed_tuples;
		}
	};
/*
	public static void main(String[] args) {

		HashSet<ArrayList<Long>> tuples = new HashSet<ArrayList<Long>>();
		tuples.add(new ArrayList<Long>(Arrays.asList(1,1,1)));
		tuples.add(new ArrayList<Long>(Arrays.asList(1,1,2)));
		tuples.add(new ArrayList<Long>(Arrays.asList(1,2,1)));
		tuples.add(new ArrayList<Long>(Arrays.asList(1,2,2)));
		tuples.add(new ArrayList<Long>(Arrays.asList(2,1,1)));
		tuples.add(new ArrayList<Long>(Arrays.asList(2,1,2)));
	ArrayList<ArrayList<Long>> domains = new ArrayList<ArrayList<Long>>();

		domains.add(new ArrayList<Long>(Arrays.asList(1,2)));
		domains.add(new ArrayList<Long>(Arrays.asList(1,2)));
		domains.add(new ArrayList<Long>(Arrays.asList(1,2)));

		HashSet<ArrayList<Long>> res =
		full_squeeze_tuples(tuples, domains, false);

		System.out.println(res);
	}
*/
	public static long free_value = Long.MIN_VALUE;

public static HashSet<ArrayList<Long>>
full_squeeze_tuples(HashSet<ArrayList<Long>> tuples, ArrayList<ArrayList<Intpair>> domains,
               boolean eager_prune) {
	HashSet<ArrayList<Long>> ret_tuples = new HashSet<ArrayList<Long>>();
	HashSet<ArrayList<Long>> tup_loop = tuples;
	while(true) {
		TupleReturn ret =
			squeeze_tuples(tup_loop, domains, eager_prune);

		for(ArrayList<Long> tup : ret.unsquashed_tuples) {
			ret_tuples.add(tup);
		}
		tup_loop = ret.squashed_tuples;

		if(tup_loop.isEmpty()) {
			return ret_tuples;
		}
	}
}

public static HashSet<ArrayList<Long>>
full_squeeze_short_tuples(HashSet<ArrayList<Long>> tuples, ArrayList<ArrayList<Intpair>> domains,
               boolean eager_prune) {
	ArrayList<HashSet<ArrayList<Long>>> seperated;
	seperated = filterTuplesByFreeValues(tuples);
	
	//System.out.println("Seperated: " + seperated);
	
	HashSet<ArrayList<Long>> ret_tuples = new HashSet<ArrayList<Long>>();
	HashSet<ArrayList<Long>> tup_loop = new HashSet<ArrayList<Long>>();
	

	for(int i = 0; i < seperated.size(); ++i) {
		//System.out.println("Trying :" + tup_loop.size() + " at depth " + i);
		tup_loop.addAll(seperated.get(i));
		//System.out.println("Added :" + seperated.get(i).size());
		
		if(!tup_loop.isEmpty()) {
			int frees = -1;
			for(ArrayList<Long> t : tup_loop) {
				int count = 0;
				for(Long l : t) {
					if(l == free_value) count++;
				}
				if(frees != -1 && count != frees) {
					//System.out.println("Inconsistent: " + frees + ":" + count);
				}
				frees = count;
			}
			//System.out.println("Frees: " + frees);
		}
		
		
		TupleReturn ret =
			squeeze_tuples(tup_loop, domains, eager_prune);

			//System.out.println("Squashed :" + ret.squashed_tuples.size());
		//System.out.println("Rejects :" + ret.unsquashed_tuples.size());

		for(ArrayList<Long> tup : ret.unsquashed_tuples) {
			ret_tuples.add(tup);
		}
		tup_loop = ret.squashed_tuples;
	}
	ret_tuples.addAll(tup_loop);
	return ret_tuples;
}


static ArrayList<HashSet<ArrayList<Long>>>
filterTuplesByFreeValues(HashSet<ArrayList<Long>> tuples) {
	ArrayList<HashSet<ArrayList<Long>>> seperated;
	seperated = new ArrayList<HashSet<ArrayList<Long>>>();
	if(tuples.isEmpty()) {
		return seperated;
	}

	int tuplength = tuples.iterator().next().size();
	for(int i = 0; i <= tuplength; ++i) {
		seperated.add(new HashSet<ArrayList<Long>>());
	}

	for(ArrayList<Long> tup : tuples) {
		int count = 0;
		for(int i = 0; i < tuplength; ++i) {
			if(tup.get(i) == Long.MIN_VALUE)
				count++;
		}
		seperated.get(count).add(tup);
	}

	return seperated;
}

static TupleReturn
squeeze_tuples(HashSet<ArrayList<Long>> tuples, ArrayList<ArrayList<Intpair>> domains,
               boolean eager_prune) {
  HashSet<ArrayList<Long>> used_tuples = new HashSet<ArrayList<Long>>();
  HashSet<ArrayList<Long>> ret_tuples = new HashSet<ArrayList<Long>>();
  for(ArrayList<Long> tuple : tuples) {
		//System.out.println("Considering: "+ tuple);
    if(!eager_prune || !used_tuples.contains(tuple)) {
			//System.out.println("A" + domains.size());
      for(int i = 0; i < domains.size(); ++i) {
        if(used_tuples.contains(tuple) && eager_prune)
          break;
			//System.out.println("B");

        if(tuple.get(i) == free_value)
          continue;
			//System.out.println("C");

        ArrayList<Long> tuple_copy = new ArrayList<Long>(tuple);
        boolean found = true;
				searchloop:
        for(Intpair pair : domains.get(i)) {
					for(long j = pair.lower; j <= pair.upper; ++j) {
	          tuple_copy.set(i, j);
						//System.out.println("Do we have: "+ tuple_copy);
	          if(!tuples.contains(tuple_copy) || (eager_prune && used_tuples.contains(tuple_copy))) {
	            found = false;
							//System.out.println("no");
	            break searchloop;
	          }
					}
        }
				
        if(found) {
					for(Intpair pair : domains.get(i)) {
          	for(long j = pair.lower; j <= pair.upper; ++j) {
            	tuple_copy.set(i, j);
            	used_tuples.add(new ArrayList<Long>(tuple_copy));
          	}
					}
          tuple_copy.set(i, free_value);
          ret_tuples.add(tuple_copy);
        }
      }
    }
  }

  HashSet<ArrayList<Long>> unsquashed_tuples = new HashSet<ArrayList<Long>>();
  for(ArrayList<Long> tup : tuples) {
    if(!used_tuples.contains(tup))
      unsquashed_tuples.add(tup);
  }
  return new TupleReturn(ret_tuples, unsquashed_tuples);
}

}
