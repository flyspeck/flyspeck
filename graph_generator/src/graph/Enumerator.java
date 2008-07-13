
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
 * Generates an Enumeration of lists.
 * See Kepler98.PartIII.Section8.page11 for an explanation.
 * It generates all lists
 *  {0=a1<= a2<= .... <= ak=outer-1), with a(k-1) <= outer-2}
 * where L is the number of vertices in the outer polygon.
 * It proceeds by taking the index of the largest aj, such that aj<outer-2,
 * then incrementing aj by 1, and setting a(j+1),...,a(k-1) = new value of aj.
 */
class Enumerator implements java.util.Enumeration {
    final private int terminalValue;
    private int[] list;

    private int[] clone(int[] X) {
        int[] Y = new int[X.length];
        for(int i = 0;i < X.length;i++)
            Y[i] = X[i];
        return Y;
    }

    public String toString() {
        String S = "";
        for(int i = 0;i < list.length;i++)
            S += " " + list[i];
        return S;
    }

    Enumerator(int inner, int outer) {
        list = new int[inner];
        terminalValue = outer - 2;
        list[list.length - 1] = terminalValue + 1; //this entry doesn't change.
        list[list.length - 2] = -1;
    }

    public boolean hasMoreElements() {
        return (largestUnfixedIndex() > 0);
    }

    /**
     * Returns the smallest integer r such that list[r] does not point to
     * the last element
     */

    private int largestUnfixedIndex() {
        int r = list.length - 2;
        while((r > 0) && (list[r] == terminalValue))
            r--;
        return r;
    }

    /**
     * interface
     */

    public Object nextElement() {
        int newvalue;
        int r = largestUnfixedIndex();
        if(r <= 0)
            return null;
        newvalue = list[r] + 1;
        for(int i = r;i < list.length - 1;i++)
            list[i] = newvalue;
        return clone(list);
    }
    public static class Test extends util.UnitTest {
        /** test case (5,7):
         * lists of length 5 of the form {0,X,X,X,6} with all X's <6
         * generate the list a second way and compare.
         */

        public void test57() {
            ArrayList L = new ArrayList();
            for(int i = 0;i < 6;i++)
                for(int j = i;j < 6;j++)
                    for(int k = j;k < 6;k++)
                        L.add(new int[] {
                            0, i, j, k, 6
                        });
            int length = L.size();
            int lengthE = 0;
            for(Enumeration E = new Enumerator(5, 7);E.hasMoreElements(); /*--*/) {
                int[] Q = (int[])E.nextElement();
                lengthE++;
                boolean match = false;
                for(int i = 0;i < L.size();i++) {
                    if(equals(Q, (int[])L.get(i))) {
                        match = true;
                        L.remove(i);
                        break;
                    }
                }
                jassert(match);
            }
            jassert(lengthE == length);
            jassert(L.size() == 0);
        }
        /**
         * helper for test57
         */

        private boolean equals(int[] list1, int[] list2) {
            if(list1.length != list2.length)
                return false;
            for(int i = 0;i < list1.length;i++)
                if(list1[i] != list2[i])
                    return false;
            return true;
        }
    }
}
