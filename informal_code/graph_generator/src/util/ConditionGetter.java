/**
 * Title:        Graph00<p>
 * Description:  <p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * Company:      University of Michigan<p>
 * @author Thomas C. Hales
 * @version 1.0
 */
package util;
import java.util.HashSet;
import java.util.ArrayList;
/**
 * General util class: has nothing to do with graphs.
 * Add objects to a  repository. (Objects can't be removed, only retrieved.)
 */
public class ConditionGetter {
    private HashSet AddedObjects = new HashSet();
    private ArrayList list = new ArrayList();

    public void add(Object A) {
        if(A != null && !AddedObjects.contains(A)) {
            AddedObjects.add(A);
            list.add(A);
        }
    }
    /**
     * Retrieve the first object placed in the repository that satisfies condition C.
     */

    public Object get(Condition C) {
        Object obj;
        for(int i = 0;i < list.size();i++) {
            obj = list.get(i);
            if(C.check(obj))
                return obj;
        }
        return null;
    }
    /**
     * Testing...
     */
    public static class Test extends util.UnitTest {

        public void test() {
            ConditionGetter C = new ConditionGetter();
            C.add(new Integer(3));
            C.add(new Integer(4));
            C.add(new Integer(5));
            C.add(new Integer(3));
            Condition cond = new Condition()  {

                public boolean check(Object obj) {
                    return obj.equals(new Integer(3));
                }
            };
            Integer A = (Integer)C.get(cond);
            jassert(A.equals(new Integer(3)));
            cond = new Condition()  {

                public boolean check(Object obj) {
                    return obj.equals(new Integer(5));
                }
            };
            A = (Integer)C.get(cond);
            jassert(A.equals(new Integer(5)));
            cond = new Condition()  {

                public boolean check(Object obj) {
                    return obj.equals(new Integer(6));
                }
            };
            A = (Integer)C.get(cond);
            jassert(A == null);
        }
        private class Vcondition implements Condition {
            private Object X;

            public Vcondition(Object X) {
                this.X = X;
            }

            public boolean check(Object O) {
                return X.equals(O);
            }
        }

        public void testConditionGetter() {
            final Object A = new Object();
            final Object B = new Object();
            ConditionGetter getter = new ConditionGetter();
            getter.add(A);
            getter.add(B);
            Condition condB = new Condition()  {

                public boolean check(Object X) {
                    return B.equals(X);
                }
            };
            Object obj = getter.get(condB);
            jassert(obj.equals(B));
            Condition condA = new Condition()  {

                public boolean check(Object X) {
                    return A.equals(X);
                }
            };
            jassert(getter.get(condA).equals(A));
            final Object C = new Object();
            Condition condC = new Condition()  {
                private final Object CX = C;

                public boolean check(Object X) {
                    return CX.equals(X);
                }
            };
            getter.add(C);
            jassert(getter.get(condC).equals(C));
            jassert(!getter.get(condC).equals(A));
            jassert(getter.get(new Vcondition(B)).equals(B));
        }
    }
}
