
/**
 * Title:        Graph00<p>
 * Description:  <p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * Company:      University of Michigan<p>
 * @author Thomas C. Hales
 * @version 1.0
 */
package graph;
public class Misc {

    private Misc() {

    }

    public static int mod(int i, int modulus) {
        int r = i % modulus;
        return (r < 0 ? r + modulus : r);
    }
    public static class Test extends util.UnitTest {

        public void test() {
            jassert(Misc.mod(-3, 4) == 1);
            jassert(Misc.mod(-7, 4) == 1);
            jassert(Misc.mod(5, 4) == 1);
            jassert(Misc.mod(4, 4) == 0);
        }
    }
}
