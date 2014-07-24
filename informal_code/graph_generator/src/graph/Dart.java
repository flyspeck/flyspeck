
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
 * A couple is a pair (v,F) of a vertex and a Face at that vertex.
 * Some algorithms in this package require an Enumeration of all of the
 * couples in a graph.
 */
public class Dart {
    private Vertex V;
    private Face F;

    public Dart(Vertex V, Face F) {
        this.V = V;
        this.F = F;
    }

    public Vertex getV() {
        return V;
    }

    public Face getF() {
        return F;
    }

    /**
     * Helper class for getDarts. check is true when the face "A" contains "V"
     */
    private static class incidence implements util.Condition {
        private Vertex V;

        public incidence(Vertex V) {
            this.V = V;
        }

        public boolean check(Object A) {
            Face F = (Face)A;
            return (V.next(F, 0) == F); //note: V.next(F,0)==F iff V lies on F.
        }
    }

    /**
     * This returns an enumeration of all Darts in Graph G in a canonical order
     * starting with firstDart.  The order is canonical in the sense that it
     * only depends on the oriented isomorphism
     * class of G (and firstDart).  That is, if there is an oriented iso
     *    G <-> G'  sending firstDart <-> firstDart', then that bijection will
     * send getDarts <-> getDarts'.
     * <p>
     * This enumeration is useful in
     * finding explicit bijections of isomorphic graphs.
     */

    public static Dart[] getDarts(Dart firstDart, Graph G) {
        /**
         * Description of algorithm:
         * Return all the couples around V0=firstDart.V, then all couples around V1, ....
         * The order for couples around firstDart.V is counterclockwise starting with firstDart.F.
         * clockwise around V1,...
         * So we need to order the vertices V0,V1,... and pick the first face to use at each vertex
         * and the rest is determined.
         * Order on V0,... = first encountered.  Order on faces at vertex = first encountered.
         */
        distinctFIFO vQueue = new distinctFIFO();
        util.ConditionGetter fQueue = new util.ConditionGetter();
        fQueue.add(firstDart.getF());
        vQueue.put(firstDart.getV());
        Collection coups = new ArrayList();
        int coupsIndex = 0;
        Vertex V;
        while((V = (Vertex)vQueue.remove()) != null) {
            Face F = (Face)fQueue.get(new incidence(V));
            for(int i = 0;i < V.size();i++) {
                Face Fx = V.next(F, i);
                coups.add(new Dart(V, Fx));
                vQueue.put(Fx.next(V, 1));
                fQueue.add(Fx);
            }
        }
        return (Dart[])coups.toArray(new Dart[coups.size()]);
    }



    /**
     * Test Code for Dart
     */
    public static class Test extends util.UnitTest {

        public void testDart() {
            String S = Formatter.testString; //see formatterString.gif
            Graph G = Graph.getInstance(new Formatter(S));
            Vertex V = null;
            int coupleCount = 0;
            for(Enumeration E = G.vertexEnumeration();E.hasMoreElements(); /*--*/) {
                Vertex W = (Vertex)E.nextElement();
                coupleCount += W.size();
                if(W.size() == 3)
                    V = W;
            }
            jassert(V.size() == 3);
            Face F = V.getAny();
            while(F.size() != 5)
                F = V.next(F, 1);
            jassert(F.size() == 5);
            Dart C = new Dart(V, F);
            Dart[] list = Dart.getDarts(C, G);
            //compute the expected number of return values;
            jassert(list.length == coupleCount);
            jassert(list[0].getV() == C.getV());
            jassert(list[0].getF() == C.getF());
            //check integrity of each couple.
            for(int i = 0;i < list.length;i++) {
                V = list[i].getV();
                F = list[i].getF();
                jassert(V.next(F, 0) == F);
                jassert(F.next(V, 0) == V);
            }
            //check that all couples are distinct.
            Hashtable table = new Hashtable(); // { V-> set of F }
            for(Enumeration E = G.vertexEnumeration();E.hasMoreElements(); /*--*/) {
                V = (Vertex)E.nextElement();
                table.put(V, new HashSet());
            }
            for(int i = 0;i < list.length;i++) {
                V = list[i].getV();
                F = list[i].getF();
                HashSet H = (HashSet)table.get(V);
                jassert(!H.contains(F));
                H.add(F);
            }
        }
    }
}
