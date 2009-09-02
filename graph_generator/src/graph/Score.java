package graph;
import java.util.*;
/**
 * We say that an operation is forced, when that operation is the only operation
 * possible (say at that given vertex).  We say that an operation is neglectable,
 * if carrying out that operation necessarily leads to a graph over the squanderTarget.
 * Thus, an operation is forced, if all other operations are neglectable.
 * <p>
 * In terms of methods.
 *  boolean Neglectable....  true is decisive, false means the test was inconclusive.
 *  boolean Forced.... true is decisive, false test was inconclusive.
 * <p>
 * All methods are final static, and objects cannot be created.
 * <p>
 * class Constants : constants but no methods.
 * class Parameter : use constants for things that don't require a graph.
 * class Score     : use constants for things that require a graph.
 */
public class Score {

    private Score() {
    };

    /**
     * The sum total of what the faces in the given graph squander.
     * @param p, scoring parameter.
     */

    final static int faceSquanderLowerBound(Graph G, Parameter p) {
        int total = 0;
        for(Enumeration E = G.faceEnumeration();E.hasMoreElements(); /*--*/) {
            Face F = (Face)E.nextElement();
            if(F.isFinal())
                total += p.squanderFace(F.size());
        }
        return total;
    }

    /**
     * includes both faceSquanderLowerBound and excesses.
     * Works fine whether all faces are isFinal or not.
     */

    final public static int squanderLowerBound(Graph G, Parameter p) {
        return faceSquanderLowerBound(G, p) + Score.ExcessNotAt(null, G, p);
    }

    /**
     * This is the excess at vertex V.
     * returns 0 if there are any temporary vertices at V.
     * @param V vertex around which excess squander is computed.
     * @param P scoring Parameter.
     */

    final static int ExcessAt(Vertex V, Parameter p) {
        if(V.nonFinalCount() > 0)
            return 0;
        int t = V.faceCount(3, 3);
        int q = V.faceCount(4, 4);
        int r = V.faceCount(5, Integer.MAX_VALUE);
        return p.pqrExcess(t, q, r);
    }
    /**
     * helper for ExcessNotAt
     * @param List
     * @param Excesses
     * @param eTable { Vertex -> excess at vertex }
     * side-effect deletes from eTable W, vertices adjacent to W, and
     * vertices opposite W through quads at W.
     * precondition: W is not null.
     */

    final static private void DeleteAround(Vertex W, Hashtable eTable) {
        // Vector List, Vector Excesses) {
        //1. remove W.
        eTable.remove(W);
        //2. remove all vertices adjacent to W.
        Face F = W.getAny();
        for(int i = 0;i < W.size();i++) {
            Face Fx = W.next(F, i);
            eTable.remove(Fx.next(W, 1));
            //2a. if Fx is a quad remove opposite as well.
            if(Fx.size() == 4)
                eTable.remove(Fx.next(W, 2));
        }
    }
    /**
     * Picks a subset of vertices and returns the sum of what is squandered around
     * these vertices.
     * The subset has the property that none is V, adjacent to V, or opposite through
     * a quad to V.
     * No two elements of the set are adjacent, or opposite through a quad to each other.
     */

    final static int ExcessNotAt(Vertex V, Graph G, Parameter p) {
        Hashtable eTable = new Hashtable(); // { vertex -> excess }
        //1. build eTable;
        for(Enumeration E = G.vertexEnumeration();E.hasMoreElements(); /*--*/) {
            Vertex W = (Vertex)E.nextElement();
            int ex = ExcessAt(W, p);
            if(ex > 0)
                eTable.put(W, new Integer(ex));
        }
        return ExcessNotAt(V, eTable, G, p);
    }

    /**
     * recursive helper for ExcessNotAt.
     * @post eTable unchanged.
     */

    final static int ExcessNotAt(Vertex V, Hashtable table, Graph G, Parameter p) {
        //1. copy Hashtable so it doesn't get modified.
        Hashtable eTable = new Hashtable();
        for(Enumeration E = table.keys();E.hasMoreElements(); /*--*/) {
            Object key = E.nextElement();
            eTable.put(key, table.get(key));
        }
        if(V != null)
            DeleteAround(V, eTable);
        //2. Get any remaining vertex then include or exclude.
        Enumeration E = eTable.keys();
        if (E.hasMoreElements()) {
            Vertex W = (Vertex)E.nextElement();
            int value = ((Integer)eTable.get(W)).intValue();
            int valueWithW = value + ExcessNotAt(W,eTable,G,p);
            eTable.remove(W);
            int valueWithoutW = ExcessNotAt(null,eTable,G,p);
            return Math.max(valueWithW,valueWithoutW);
        }
        //3. no remaining vertices
        return 0;
    }

    /**
     * An upper bound on the score of the Graph.
     * @param p scoring parameter.
     * precondition: all faces have isFinal attribute true.
     */

    final public static int scoreUpperBound(Graph G, Parameter p) {
        util.Eiffel.precondition(Structure.nonFinalCount(G) == 0);
        int temp = 0;
        for(Enumeration E = G.faceEnumeration();E.hasMoreElements(); /*--*/) {
            Face F = (Face)E.nextElement();
            if(F.isFinal())
                temp += Constants.getFixedScoreFace(F.size());
        }
        return temp;
    }
    /**
     * Unusual parameter passing.
     * @param V Vertex under consideration
     * @param p scoring parameter.
     * @param tri number of additional triangles.
     * @param quad = number of additional quads,
     * @param excep=0 means no exceptionals added.
     * @param excep=n>0 means one exceptional, an n-gon added at v.
     * @param temp = number of additional temps.
     * return false inconclusive
     * return true : this parameter set is neglectable
     */

    final static boolean neglectableModification(Graph G, int tri, int quad, int excep, int temp, Vertex V, Parameter p) {
        //1. set constants.
        int t = tri + V.faceCount(3, 3);
        int q = quad + V.faceCount(4, 4);
        int tempX = temp + V.nonFinalCount();
        int e = V.faceCount(5, Integer.MAX_VALUE);
        if(excep > 0)
            e++;
        //2. if vertex is too crowded, it is neglectable.
        if((e > 0) && (t + q + tempX + e > Constants.getFaceCountMaxAtExceptionalVertex()))
            return true;
        if((e == 0) && (t + q + tempX + e > Constants.getFaceCountMax()))
            return true;
        //3. if squanders more than the target, it is neglectable.
        int sq = faceSquanderLowerBound(G, p) + (excep > 0 ? p.squanderFace(excep) : 0) + tri * p.squanderFace(3) + quad * p.squanderFace(4);
        if(sq >= Constants.getSquanderTarget())
            return true;
        if(sq + ExcessNotAt(null, G, p) >= Constants.getSquanderTarget())
            return true;
        int excessAtV = p.squanderForecast(t, q, tempX) - t * p.squanderFace(3) - q * p.squanderFace(4);
        /** change 11/30/05 **/
        int extraExceptSq = p.squanderFaceStartingAt(5);
        boolean noExceptAtV = ((e==0) && (tempX ==0)) || (t + q + tempX + e > Constants.getFaceCountMaxAtExceptionalVertex()) ||
          (sq + ExcessNotAt(null,G,p) + extraExceptSq >= Constants.getSquanderTarget());

        if((noExceptAtV) && ((sq + ExcessNotAt(V, G, p) + excessAtV >= Constants.getSquanderTarget())))
            return true;
        /** end change 11/30/05 **/
        //4. tests were inconclusive.
        return false;
    }
    /**
     * helper for neglectable(G,p).
     * return true if the graph is bad for reasons of scoring.
     * Tests:
     *      (1) too many or too few vertices.
     *      (2) overcrowded vertices.
     *      (3) squander or score beyond targets.
     * return false means inconclusive.
     * precondition: G is final.
     */

    final private static boolean neglectableFinal(Graph G, Parameter p) {
        //0. test precondition.
        util.Eiffel.precondition(Structure.isFinal(G));
        //1. count number of vertices.
        /*
        if(G.vertexSize() > Constants.getVertexCountMax())
            return true;
        if(G.vertexSize() < Constants.getVertexCountMin())
            return true;
        */ // Jan 2002.
        //2. look for overcrowded vertices.
        for(Enumeration E = G.vertexEnumeration();E.hasMoreElements(); /*--*/) {
            Vertex V = (Vertex)E.nextElement();
            int ex = V.faceCount(5, Integer.MAX_VALUE);
            if((ex > 0) && (V.size() > Constants.getFaceCountMaxAtExceptionalVertex()))
                return true;
            if((ex == 0) && (V.size() > Constants.getFaceCountMax()))
                return true;
        }
        //3. look for squander or score beyond target.
        if(ExcessNotAt(null, G, p) + faceSquanderLowerBound(G, p) > Constants.getSquanderTarget())
            return true;
        if(scoreUpperBound(G, p) < Constants.getScoreTarget())
            return true;
        //4. tests are inconclusive.
        return false;
    }

    /**
     *
     */
    public static boolean neglectable(Graph G, Parameter param) {
	boolean QL = false;
        if(Score.neglectableByBasePointSymmetry(G))
            return true;
        /*
        if (Structure.isFinal(G)) {
          if (G.vertexSize() > Constants.getVertexCountMax())
            return true;
          if (G.vertexSize() < Constants.getVertexCountMin())
            return true;
        }
        */
        if(Constants.getExcludePentQRTet() && Structure.has11Type(G))
            return true;
        if(Structure.isFinal(G) && Score.neglectableFinal(G, param))
            return true;
        if (QL && Structure.isFinal(G) && Structure.hasAdjacent40(G))
            return true;
        return false;
    }
    /**
     * Gives an upper bound on the number of sides a face can have.
     */

    final static int polyLimit(Graph G, Parameter p) {
        int polylimit = p.maxGon();
        int lb = faceSquanderLowerBound(G, p) + ExcessNotAt(null, G, p);
        while((lb + p.squanderFace(polylimit) >= Constants.getSquanderTarget()) && (polylimit > 0))
            polylimit--;
        return polylimit;
    }

    /**
     * poly is a list of vertices to appear in a new face about to be added to F.
     * Returns true if this new face would definitely be bad.
     * Return false if inconclusive.
     */

    final static boolean neglectable(Vertex[] poly, Face F, Graph G, Parameter p) {
        int ngon = poly.length;
        for(int i = 0;i < poly.length;i++) {
            if(poly[i] == null)
                continue;
            //1. initialize tri,quad,excep as in neglectableModification method.
            int temp = -1;
            int excep = (ngon > 4 ? ngon : 0);
            int quad = (ngon == 4 ? 1 : 0);
            int tri = (ngon == 3 ? 1 : 0);
            //2. get size of forward looking ngon.
            int index = Misc.mod(i + 1, ngon);
            while(poly[index] == null)
                index = Misc.mod(index + 1, ngon);
            int forwardNgon = F.directedLength(poly[i], poly[index]) + Misc.mod(index - i, ngon);
            if(forwardNgon == 3)
                tri += 1;
            if(forwardNgon > 3)
                temp += 1;
            //3. get size of backward looking ngon.
            index = Misc.mod(i - 1, ngon);
            while(poly[index] == null)
                index = Misc.mod(index - 1, ngon);
            int backwardNgon = F.directedLength(poly[index], poly[i]) + Misc.mod(i - index, ngon);
            if(backwardNgon == 3)
                tri += 1;
            if(backwardNgon > 3)
                temp += 1;
            if(Score.neglectableModification(G, tri, quad, excep, temp, poly[i], p))
                return true;
        }
        return false;
    }
    /**
     * return true if the only way to stay under the target is to replace every
     * temp face at V with a single triangle at V, filling three consecutive vertices
     * of the temp face.
     * <p>
     * return false means the test is inconclusive.
     * @param p Scoring parameter
     * @param V Vertex
     */

    final static boolean ForcedTriangleAt(Graph G, Vertex V, Parameter p) {
        //1. compute constants.
        int t = V.faceCount(3, 3);
        int q = V.faceCount(4, 4);
        int tempX = V.nonFinalCount();
        int e = V.faceCount(5, Integer.MAX_VALUE);
        int fsq = faceSquanderLowerBound(G, p);
        int fsqred = fsq - q * p.squanderFace(4) - t * p.squanderFace(3);
        int target = Constants.getSquanderTarget();
        int excessNot = ExcessNotAt(V, G, p);
        //2. case of no exceptionals at V.
        if(e == 0) {
            if(fsq + p.squanderFaceStartingAt(5) <= target)
                return false;
            if(p.squanderForecast(t, q + 1, tempX - 1) + fsqred + excessNot <= target)
                return false;
            if(p.squanderForecast(t + tempX + 1, q, 0) + fsqred + excessNot <= target)
                return false;
            return true;
        }
        //3. case of exceptionals at V.
        int nextface = p.squanderFaceStartingAt(4);
        if(fsq + excessNot + nextface <= target)
            return false;
        if(t + tempX + q + e + 1 <= Constants.getFaceCountMaxAtExceptionalVertex())
            return false;
        return true;
    }

    /**
     * helper for hashVertex
     */

    static private long pow(int exp) {
        long r = 1;
        for(int i = 0;i < exp;i++)
            r *= base;
        return r;
    }

    /**
     * helper for neglectableByBasePointSymmetry.
     * hash = sum_i^size base^(facesize#i)
     * base is large enough that that largest hash vertex will appear on a largest face
     */

    static public long hashVertex(Vertex V) {
        long hash = 0;
        Face F = V.getAny();
        for(int i = 0;i < V.size();i++)
            hash += pow(V.next(F, i).size());
        return hash;
    }
    final private static long base = Constants.getFaceCountMax() * 2;


    /**
     * By construction, when there are exceptional regions, the
     * baseVertex is chosen in the graph to be one on a face with the
     * most sides.  Take the one with greatest hash.
     */

    static boolean neglectableByBasePointSymmetry(Graph G) {
        Vertex bV = G.getBaseVertex();
        if(bV == null)
            return false;
        long hashBV = hashVertex(bV);
        for(Enumeration E = G.vertexEnumeration();E.hasMoreElements(); /*--*/) {
            Vertex V = (Vertex)E.nextElement();
            if(V.nonFinalCount() == 0 && hashVertex(V) > hashBV)
                return true;
        }
        return false;
    }
    /**
     * Would having a new straight line from A to B in Face F cause any problems??
     * true means it would definitely be bad.
     *   Tests:
     *   (1) if A and B are already adjacent by an edge not on the face, a double join would be created.
     *   (2) Is a triangle with an enclosed vertex created?
     * false means that the tests are inconclusive.
     * precondition: A and B lie on F.
     */

    static boolean neglectableEdge(Vertex A, Vertex B, Face F) {
        //1. Are A and B already adjacent by an edge not on F?
        if(F.size() < 5)
            return false;
        int AtoB = F.directedLength(A, B);
        int BtoA = F.directedLength(B, A);
        if(Math.min(AtoB, BtoA) < 2)
            return false; // A and B are adjacent on F.
        for(int i = 0;i < A.size();i++) {
            if(A.next(F, i).next(A, 1) == B)
                return true; // adjacent condition fulfilled
        }
        //2. Is a trianlge with an enclosed vertex created?
        if(Math.min(AtoB, BtoA) < 3)
            return false; // can return false whenever we please.
        Vertex[] vA = new Vertex[A.size()];
        Vertex[] vB = new Vertex[B.size()];
        for(int i = 0;i < A.size();i++)
            vA[i] = A.next(F, i).next(A, 1); //array of neighbors.
        for(int i = 0;i < B.size();i++)
            vB[i] = B.next(F, i).next(B, 1);
        for(int i = 0;i < vA.length;i++)
            for(int j = 0;j < vB.length;j++)
                if(vA[i] == vB[j])
                    return true; // triangle with enclosed vertex found.
        //3. give up, inconclusive.
        return false;
    }
    public static class Test extends util.UnitTest {

        public void testAgainstOct() {
            int series = graphDispatch.ALL;
            Parameter p = Parameter.getExceptionalCase(8);
            for(int i = 0;i < graphDispatch.size(series);i++) {
                String S = graphDispatch.getArchiveString(series, i);
                Graph G = Graph.getInstance(new Formatter(S));
                // these should never have made it onto the list.
                if(i != 17 && i != 19 && i != 20 && i != 22 && i != 23 && i != 24 && i != 27 && i != 31)
                    jassert(Score.scoreUpperBound(G, p) >= Constants.getScoreTarget(), " " + i);
                int fsq = Score.faceSquanderLowerBound(G, p);
                int ena = Score.ExcessNotAt(null, G, p);
                Invariant inv = new Invariant(G);
                long hash = inv.getHash();
                if(i!= 43 && i != 42 && i != 41 && i != 40
                    && i!= 39 && i != 38 && i != 36 && i != 35
                    && i!= 34 && i!= 33 && i!= 32 && i != 10 && i != 9 && i != 8)
                    {} // jassert(fsq + ena < Constants.getSquanderTarget()," "+i);
            }
        }
    }
}
