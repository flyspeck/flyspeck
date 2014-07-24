
/**
 * Title:        Graph00<p>
 * Description:  <p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * Company:      University of Michigan<p>
 * @author Thomas C. Hales
 * @version 1.0
 */
package graph;
import java.util.*;

/**
 * Keeps track of a collection of Invariant objects with a hashtable.
 */
public class InvariantSet {
    private HashMap H = new HashMap(); //{ hash -> Invariant arraylist}

    public InvariantSet() {

    }

    /**
     * return true if there is an isomorphic invariant in H.
     */

    public boolean contains(Invariant inv) {
        Long hash = new Long(inv.getHash());
        if(!H.containsKey(hash))
            return false;
        ArrayList list = (ArrayList)H.get(hash);
        for(int i = 0;i < list.size();i++) {
            if(inv.Isomorphic((Invariant)list.get(i)))
                return true;
        }
        return false;
    }

    /**
     * The key set for the invariants.
     */

    public Set keySet() {
        return H.keySet();
    }

    /**
     * The values for a given key
     */

    public Collection get(Long hash) {
        return (Collection)H.get(hash);
    }

    /**
     * Adds the invariant. Duplicate entries are possible.
     */

    public void add(Invariant inv) {
        Long hash = new Long(inv.getHash());
        ArrayList list;
        if(H.containsKey(hash))
            list = (ArrayList)H.get(hash);
        else {
            list = new ArrayList();
            H.put(hash, list);
        }
        list.add(inv);
    }

    public int size() {
        Collection C = H.values();
        ArrayList[] list = (ArrayList[])C.toArray(new ArrayList[C.size()]);
        int total = 0;
        for(int i = 0;i < list.length;i++)
            total += list[i].size();
        return total;
    }

    public Collection values() {
        Collection C = H.values();
        ArrayList[] list = (ArrayList[])C.toArray(new ArrayList[C.size()]);
        Collection A = new ArrayList();
        for(int i = 0;i < list.length;i++)
            for(int j = 0;j < list[i].size();j++)
                A.add(list[i].get(j));
        return A;
    }


    /***
     * Testing.....
     */
    public static class Test extends util.UnitTest {

        public void testAdd() {
            String Astring = archive.getArchiveString(5);
            String Bstring = archive.getArchiveString(6);
            Invariant A = new Invariant(Graph.getInstance(new Formatter(Astring)));
            Invariant B = new Invariant(Graph.getInstance(new Formatter(Bstring)));
            InvariantSet IS = new InvariantSet();
            IS.add(A);
            jassert(IS.contains(A));
            jassert(IS.size() == 1);
            jassert(!IS.contains(B));
            IS.add(A);
            jassert(IS.size() == 2);
            IS.add(B);
            jassert(IS.size() == 3);
            jassert(IS.contains(B));
            Graph GB = Graph.getInstance(new Formatter(Bstring));
            Graph GBmirror = GB.copy(true, new Vertex[0], new Face[0]);
            Invariant Bmirror = new Invariant(GBmirror);
            jassert(IS.contains(Bmirror));
            Graph GBclone = GB.copy(false, new Vertex[0], new Face[0]);
            jassert(IS.contains(new Invariant(GBclone)));
            jassert(IS.size() == 3);
            Collection C = IS.values();
            Invariant[] list = (Invariant[])C.toArray(new Invariant[C.size()]);
            jassert(list.length == 3);
            for(int i = 0;i < 3;i++)
                jassert(list[i].Isomorphic(A) || list[i].Isomorphic(B));
        }
    }
}
