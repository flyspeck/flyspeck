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
                total += p.tableWeightD(F.size());
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
        return ExcessNotAtTable(V, eTable, G, p);
    }

    /**
     * recursive helper for ExcessNotAt.
     * @post eTable unchanged.
     */

    final static int ExcessNotAtTable(Vertex V, Hashtable table, Graph G, Parameter p) {
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
            int valueWithW = value + ExcessNotAtTable(W,eTable,G,p);
            eTable.remove(W);
            int valueWithoutW = ExcessNotAtTable(null,eTable,G,p);
            return Math.max(valueWithW,valueWithoutW);
        }
        //3. no remaining vertices
        return 0;
    }

    /**
     * Unusual parameter passing.
     * @param V Vertex under consideration
     * @param p scoring parameter.
     * @param triDelta number of additional triangles.
     * @param quadDelta = number of additional quads,
     * @param excepSz=0 means no exceptionals added.
     * @param excepSz=n>0 means one exceptional, an n-gon added at v.
     * @param tempDelta = number of additional temps (can be negative to take away from V).
     * return false inconclusive
     * return true : this parameter set is neglectable
     */

    final static boolean neglectableModification
	(Graph G, int triDelta, int quadDelta, int excepSz, int tempDelta, Vertex V, Parameter p) {
        //1. set constants.
	int tgt = Constants.getSquanderTarget();
        int triX = triDelta + V.faceCount(3, 3);
        int quadX = quadDelta + V.faceCount(4, 4);
        int tempX = tempDelta + V.nonFinalCount();
        int eX = V.faceCount(5, Integer.MAX_VALUE);
        if(excepSz > 0)
            eX++;
        util.Eiffel.precondition(tempX >= 0);
        util.Eiffel.precondition(V.nonFinalCount() > 0);

        //2. if vertex is too crowded, it is neglectable.
        if((eX == 0) && (triX + quadX + tempX > Constants.getNodeCardMax()))
            return true;
        if((eX > 0) && (triX + quadX + tempX + eX > Constants.getNodeCardMaxAtExceptionalVertex()))
            return true;

        //3. if squanders more than the target, it is neglectable.
        int faceSqX = faceSquanderLowerBound(G, p) + triDelta * p.tableWeightD(3) + 
	    quadDelta * p.tableWeightD(4) +  (excepSz > 0 ? p.tableWeightD(excepSz) : 0) ;
	//redundant:
        if(faceSqX >= tgt)
            return true;
	//strengthening of previous:
	int excess = ExcessNotAt(null, G, p);
        if(faceSqX + excess >= tgt)
            return true;
	/** change 11/30/05, 9/6/09 **/
	//4. if no exceptionals at V, and over target, it is neglectable.
	int extraExceptSq = p.tableWeightDStartingAt(5);
	boolean noExceptAtV = (eX==0) && 
	     ((tempX ==0) || 
	      (triX + quadX + tempX > Constants.getNodeCardMaxAtExceptionalVertex()) ||
	      (faceSqX + excess + extraExceptSq >= tgt));
	if (noExceptAtV) {
	    int pqSquAtV = p.squanderForecastPureB(triX, quadX, tempX) ;
	    int faceSqXNotV = faceSqX -triX * p.tableWeightD(3) - quadX * p.tableWeightD(4);
	    if(faceSqXNotV + ExcessNotAt(V, G, p) + pqSquAtV >= tgt)
		return true;
	}
        /** end change 11/30/05 **/
        //5. tests were inconclusive.
        return false;
    }

    /**
     * helper for neglectableGeneral(G,p).
     * return true if the graph is bad for reasons of scoring.
     * Tests:
     *      (1) too many or too few vertices.
     *      (2) overcrowded vertices.
     *      (3) squander or score beyond targets.
     * return false means inconclusive.
     * precondition: G is final.
     */

    final public static boolean neglectableFinal(Graph G, Parameter p) {
        //0. test precondition.
        util.Eiffel.precondition(Structure.isFinal(G));
        //1. count number of vertices.
        if(G.vertexSize() > Constants.getVertexCountMax())
            return true;
        if(G.vertexSize() < Constants.getVertexCountMin())
            return true;
        //2. look for overcrowded vertices.
        for(Enumeration E = G.vertexEnumeration();E.hasMoreElements(); /*--*/) {
            Vertex V = (Vertex)E.nextElement();
            int ex = V.faceCount(5, Integer.MAX_VALUE);
            if((ex > 0) && (V.size() > Constants.getNodeCardMaxAtExceptionalVertex()))
                return true;
            if((ex == 0) && (V.size() > Constants.getNodeCardMax()))
                return true;
        }
        //3. look for squander or score at least target.
        if(ExcessNotAt(null, G, p) + faceSquanderLowerBound(G, p) >= Constants.getSquanderTarget())
            return true;
        //if(scoreUpperBound(G, p) < Constants.getScoreTarget())
        //    return true;
	//4. look for special structures:
       if(Constants.getExcludePentQRTet() && Structure.has11Type(G))
            return true;
        if (Constants.getExclude2inQuad() && Structure.hasAdjacent40(G))
            return true;
	if (Constants.getExcludeDegree2() && Structure.hasDegree2(G))
	    return true;
        //5. tests are inconclusive.
        return false;
    }

    /**
     *
     */
    public static boolean neglectableGeneral(Graph G, Parameter param) {
        if(Score.neglectableByBasePointSymmetry(G))
            return true;
        if(Structure.isFinal(G) && Score.neglectableFinal(G, param))
            return true;
        return false;
    }
    /**
     * Gives an upper bound on the number of sides a new face can have.
     */

    final static int polyLimit(Graph G, Parameter p) {
        int polylimit = p.maxGon();
        int lb = faceSquanderLowerBound(G, p) + ExcessNotAt(null, G, p);
        while((lb + p.tableWeightD(polylimit) >= Constants.getSquanderTarget()) && (polylimit > 0))
            polylimit--;
        return polylimit;
    }

    /**
     * poly is a list of vertices to appear in a new face about to be added to F.
     * Returns true if this new face would definitely be bad.
     * Return false if inconclusive.
     */

    final static boolean neglectablePoly(Vertex[] poly, Face F, Graph G, Parameter p) {
	boolean TL = Constants.getExclude1inTri();
        int ngon = poly.length;
        for(int i = 0;i < poly.length;i++) {
            if(poly[i] == null)
                continue;
            //1. initialize triDelta,quadDelta,excep as in neglectableModification method.
            int tempDelta = -1;
            int excepSz = (ngon > 4 ? ngon : 0);
            int quadDelta = (ngon == 4 ? 1 : 0);
            int triDelta = (ngon == 3 ? 1 : 0);
            //2. get size of forward looking ngon.
	    {
            int index = Misc.mod(i + 1, ngon);
            while(poly[index] == null)
                index = Misc.mod(index + 1, ngon);
            int forwardNgon = F.directedLength(poly[i], poly[index]) + Misc.mod(index - i, ngon);
	    if (forwardNgon > 2) tempDelta += 1;
	    if (TL && (forwardNgon == 3)) { triDelta += 1; tempDelta -= 1; }
	    }
            //3. get size of backward looking ngon.
	    {
            int index = Misc.mod(i - 1, ngon);
            while(poly[index] == null)
                index = Misc.mod(index - 1, ngon);
            int backwardNgon = F.directedLength(poly[index], poly[i]) + Misc.mod(i - index, ngon);
	    if (backwardNgon > 2) tempDelta += 1;
	    if (TL && (backwardNgon == 3)) { triDelta += 1; tempDelta -= 1; }
	    }
            if(Score.neglectableModification(G, triDelta, quadDelta, excepSz, tempDelta, poly[i], p))
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
        int tgt = Constants.getSquanderTarget();

        int triX = V.faceCount(3, 3);
        int quadX = V.faceCount(4, 4);
        int tempX = V.nonFinalCount();
        int eX = V.faceCount(5, Integer.MAX_VALUE);
        int fsq = faceSquanderLowerBound(G, p);
        int excessNotV = ExcessNotAt(V, G, p);
        //2. case of no exceptionals at V.
        if(eX == 0) {
	    int fsqNotV = fsq - quadX * p.tableWeightD(4) - triX * p.tableWeightD(3);
           if(p.squanderForecastPureB(triX, quadX + 1, tempX - 1) + fsqNotV + excessNotV < tgt)
                return false;
            if(p.squanderForecastPureB(triX + tempX + 1, quadX, 0) + fsqNotV + excessNotV < tgt)
                return false;
	    if (p.maxGon() < 5) // 5/2010.
		return true;
            if(fsq + p.tableWeightDStartingAt(5) < tgt)
                return false;
            return true;
        }
        //3. case of exceptionals at V.
	else {
        int nextface = p.tableWeightDStartingAt(4);
        if(fsq + excessNotV + nextface < tgt)
            return false;
        if(triX + tempX + quadX + eX  < Constants.getNodeCardMaxAtExceptionalVertex())
            return false;
        return true;
	}
    }


    /**
     * By construction, when there are exceptional regions, the
     * baseVertex is chosen in the graph to be one on a face with the
     * most sides.  Take the one with greatest hash.
     */

    static boolean neglectableByBasePointSymmetry(Graph G) {
        Vertex bV = G.getBaseVertex();
	// This fixes error exposed in Isabelle formal verfication by T. Nipkow.
	// BUG FIXED OCT 1, 2010, 8:38pm.
	// The second disjunct was missing, which resulted in 2 dropped cases.
        if ((bV == null) || (bV.nonFinalCount() > 0))   
            return false;
        long hashBV = Structure.hashVertex(bV);
        for(Enumeration E = G.vertexEnumeration();E.hasMoreElements(); /*--*/) {
            Vertex V = (Vertex)E.nextElement();
            if(V.nonFinalCount() == 0 && Structure.hashVertex(V) > hashBV)
                return true;
        }
        return false;
    }
    /**
     * Would having a new straight line from A to B in Face F cause any problems??
     * true means it would definitely be bad.
     *   Tests:
     *   (1) if A and B are already adjacent by an edge not on the face, 
     *  a double join would be created.
     *  // deprecated: (2) Is a triangle with an enclosed vertex created?
     * false means that the tests are inconclusive.
     * precondition: A and B lie on F.
     */

    static boolean neglectableJoin(Vertex A, Vertex B, Face F) {
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
        //2. Give up, inconclusive.
	return false;
    }
    public static class Test extends util.UnitTest {

        public void testAgainstOct() {
            int series = 0;
            Parameter p = Parameter.getGeneralCase(8);
            for(int i = 0;i < archive.size();i++) {
                String S = archive.getArchiveString( i);
                Graph G = Graph.getInstance(new Formatter(S));
                int fsq = Score.faceSquanderLowerBound(G, p);
                int excess = Score.ExcessNotAt(null, G, p);
                Invariant inv = new Invariant(G);
                long hash = inv.getHash();
                if(i!= 43 && i != 42 && i != 41 && i != 40
                    && i!= 39 && i != 38 && i != 36 && i != 35
                    && i!= 34 && i!= 33 && i!= 32 && i != 10 && i != 9 && i != 8)
                    {} // jassert(fsq + excess < Constants.getSquanderTarget()," "+i);
            }
        }
    }
}
