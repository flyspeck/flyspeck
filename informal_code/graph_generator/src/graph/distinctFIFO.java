
/**
 * Title:        Graph00<p>
 * Description:  <p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * Company:      University of Michigan<p>
 * @author Thomas C. Hales
 * @version 1.0
 */
package graph;

/**
 * General utility class: has nothing to do with graphs.
 * FIFO data structure.  Adding nulls is ignored.
 * Adding an object that was previously added has no effect.
 * That is, the stream of non-null objects returned by calls to get are all distinct.
 * Example:
 *  add(a); add(b); add(null); add(b); add(c); add(a);
 *  get()->a; get()->b; get()->c; get()->null;
 */
public class distinctFIFO {
    private java.util.LinkedList vlist = new java.util.LinkedList();
    private java.util.Collection returnSet = new java.util.HashSet();

    public distinctFIFO() {

    }

    public void put(Object obj) {
        vlist.addLast(obj);
    }

    public Object remove() {
        while(!vlist.isEmpty()) {
            Object obj = vlist.removeFirst();
            //1. discard objects if null or previously returned.
            if(obj == null)
                continue;
            if(returnSet.contains(obj))
                continue;
            //2. otherwise return it.
            returnSet.add(obj);
            return obj;
        }
        return null;
    }
    public static class Test extends util.UnitTest {

        public void test() {
            distinctFIFO fifo = new distinctFIFO();
            Object A = new Object();
            Object B = new Object();
            Object C = new Object();
            fifo.put(A);
            fifo.put(B);
            fifo.put(null);
            fifo.put(B);
            fifo.put(C);
            fifo.put(A);
            jassert(A.equals(fifo.remove()));
            jassert(B.equals(fifo.remove()));
            jassert(C.equals(fifo.remove()));
            jassert(null == fifo.remove());
            jassert(null == fifo.remove());
        }
    }
}
