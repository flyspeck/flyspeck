package graph;
import java.util.*;

/**
 * Title:        Graph00
 * Description:
 * Copyright:    Copyright (c) Thomas C. Hales
 * Company:      University of Michigan
 * @author Thomas C. Hales
 * @version 1.0
 */

 /**
  * This is a version of InvariantSet for debugging purposes.
  * It does not save the Graphs, only the invariants.
  * get returns an empty collection.
  * The method "values" returns an empty collection.
  * The method "contains" returns true, if the hash code matches.
  */

public class InvariantSetThin extends InvariantSet {

    private HashSet Hs = new HashSet();

    public InvariantSetThin() {
      super();
    }

    /**
     * return true if there is an isomorphic invariant in H.
     */

    public boolean contains(Invariant inv) {
        Long hash = new Long(inv.getHash());
        return Hs.contains(hash);
    }

    /**
     * The key set for the invariants.
     */

    public Set keySet() {
        return Hs;
    }

    /**
     * The values for a given key
     */

    public Collection get(Long hash) {
        return new HashSet();
    }

    /**
     * Adds the invariant. Duplicate entries are possible.
     */

    public void add(Invariant inv) {
        Long hash = new Long(inv.getHash());
        Hs.add(hash);
    }

    public int size() {
        return Hs.size();
    }

    public Collection values() {
      return new HashSet();
    }

}