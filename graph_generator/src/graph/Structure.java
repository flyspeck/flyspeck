
/**
 * Title:        Graph00<p>
 * Description:  <p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * Company:      University of Michigan<p>
 * @author Thomas C. Hales
 * @version 1.0
 */
package graph;
import java.util.Enumeration;

/**
 * Looks at structural properties of Graphs.
 * All classes are static final.
 */
public class Structure {

    /**
     * The number of nonFinal Faces on G
     */

    final static int nonFinalCount(Graph G) {
        int count = 0;
        for(Enumeration E = G.faceEnumeration();E.hasMoreElements(); /*--*/) {
            Face F = (Face)E.nextElement();
            if(!F.isFinal())
                count++;
        }
        return count;
    }

    /**
     * Returns true if at the vertex V there is 1 triangle, 1 pentagon (both final)
     * and nothing else.
     */

    final private static boolean has11Type(Vertex V) {
        // true if vertex i has 1 pentagon, 1 triangle and nothing else.
        if(V.nonFinalCount() > 0)
            return false;
        if(V.size() != 2)
            return false;
        Face F1 = V.getAny();
        if(F1.size() != 3)
            F1 = V.next(F1, 1);
        if(F1.size() != 3)
            return false;
        if(V.next(F1, 1).size() != 5)
            return false;
        return true;
    }

    /**
     * Returns true if some vertex has11Type
     */

    final static boolean has11Type(Graph G) {
        for(Enumeration E = G.vertexEnumeration();E.hasMoreElements(); /*--*/) {
            if(has11Type((Vertex)E.nextElement()))
                return true;
        }
        return false;
    }

    /**
     * helper for hasAdjacent40.
     * Returns true if the vertex is surrounded by final faces, of which there
     * are 4, all triangles.
     */

    private final static boolean has40(Vertex V) {
        if (V.nonFinalCount()>0) return false;
        if (V.faceCount(4,Integer.MAX_VALUE)>0) return false;
        if (V.faceCount(3,3)!=4) return false;
        return true;
    }

    /**
     * Returns true if adjacent vertices have type triangle=4,quad=0,except=0.
     */

    final static boolean hasAdjacent40(Graph G) {
        for (Enumeration E = G.vertexEnumeration();E.hasMoreElements();/*--*/) {
            Vertex V = (Vertex)E.nextElement();
            if (!has40(V)) continue;
            util.Eiffel.jassert(V.size()==4);
            Face F = V.getAny();
            for (int i=0;i<V.size();i++) {
                Vertex W = V.next(F,i).next(V,1); // V,W are adjacent.
                if (has40(W)) return true;
            }
        }
        return false;
    }

    /**
     * helper for hasType.
     * returns true if the two lists are the same, up to dihedral ordering.
     */
    final static private boolean dihedrallyEquivalent(int[] A,int[] B) {
        if (A.length!=B.length) return false;
        //1. check if cyclic equivalent.
        for (int i=0;i<A.length;i++) {
            boolean match=true;
            for (int j=0;j<A.length;j++) {
                if (A[j]!= B[Misc.mod(i+j,B.length)])
                    match = false;
            }
            if (match) return true;
        }
        //2. check if anti-cyclic equivalent.
        for (int i=0;i<A.length;i++) {
            boolean match=true;
            for (int j=0;j<A.length;j++) {
                if (A[j]!= B[Misc.mod(i-j,B.length)])
                    match = false;
            }
            if (match) return true;
        }
        return false;
    }

    /**
     * helper for hasType for a graph.
     * Type is as in Constants.quadCases. For example, {3,4,3,4} is
     * a vertex with 4 faces, alternating with 3 and 4 sides.
     */
    final private static boolean hasType(Vertex V,int[] type) {
        if (V.size()!= type.length) return false;
        if (V.faceCount(5,Integer.MAX_VALUE)>0) return false;
        int tri = V.faceCount(3,3);
        int triType=0;
        for (int i=0;i<type.length;i++)
            if (type[i]==3) triType++;
        if (tri!=triType) return false;
        int[] Vtype = new int[V.size()];
        Face F = V.getAny();
        for (int i=0;i<Vtype.length;i++) {
            Vtype[i]=V.next(F,i).size();
        }
        return dihedrallyEquivalent(Vtype,type);
    }

    /**
     * Type is an array giving the structure around a vertex;
     * True if it contains the given face sequence size, up to dihedral symmetry.
     * precondtion G isFinal.
     */
    final static boolean hasType(Graph G,int[] type) {
        for (Enumeration E=G.vertexEnumeration();E.hasMoreElements();/*--*/) {
            Vertex V = (Vertex) E.nextElement();
            if (V.nonFinalCount()>0) continue;
            if (hasType(V,type))
                return true;
        }
        return false;
    }

    /**
     * returns the number of sides on the face with the most sides at V.
     * Does not consider whether faces are isFinal or not.
     */

    final static int highGon(Vertex V) {
        int high = 0;
        Face F = V.getAny();
        for(int k = 0;k < V.size();k++) {
            int temp = V.next(F, k).size();
            if(temp > high)
                high = temp;
        }
        return high;
    }

    /**
     * Selects one nonFinal face with the smallest size.
     * returns null iff all faces are isFinal
     */

    static Face getSmallestTempFace(Graph G) {
        int outer = Integer.MAX_VALUE;
        Face pick = null;
        for(Enumeration E = G.faceEnumeration();E.hasMoreElements(); /*--*/) {
            Face F = (Face)E.nextElement();
            if((!F.isFinal()) && (F.size() < outer)) {
                outer = F.size();
                pick = F;
            }
        }
        return pick;
    }


    /**
     * returns the vertex around Face F of minimal height.
     */

    final static Vertex selectMinimalVertex(Face F) {
        int minheight = Integer.MAX_VALUE;
        int index = -1;
        Vertex V = F.getAny();
        for(int i = 0;i < F.size();i++) {
            int h = F.next(V, i).getHeight();
            if(h < minheight) {
                minheight = h;
                index = i;
            }
        }
        return F.next(V, index);
    }


    /**
     * @param G Graph,
     * @post side-effect faces of G with 3 sides are made final (if G has more than 3 vertices).
     */

    static void makeTrianglesFinal(Graph G) {
        for(Enumeration E = G.faceEnumeration();E.hasMoreElements(); /*--*/) {
            Face F = (Face)E.nextElement();
            if(G.vertexSize() > 3 && F.size() == 3)
                F.setFinal(true);
        }
    }

    /**
     * @param G Graph,
     * @return true if all faces are final.
     */

    static boolean isFinal(Graph G) {
        return (nonFinalCount(G) == 0);
    }




    /**
     * more test code in GraphTest...
     */
    public static class Test extends util.UnitTest {

        public void structureHas11Type() {
            //1. Face F1
            Graph G = Graph.getInstance(5);
            jassert(GraphTest.Test.getFace(1, G).size() == 5);
            //F2.
            Face F = GraphTest.Test.getAddOn(G);
            Vertex V = G.getBaseVertex();
            Vertex[] V0 = new Vertex[] {
                F.next(V, -1), V, F.next(V, 1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(Structure.has11Type(V0[1]));
            jassert(!Structure.has11Type(V0[0]));
            jassert(Structure.has11Type(G));
        }
    }
}
