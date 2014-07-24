/**
 * Title:        <p>
 * Description:  <p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * Company:      EventMonitor, Inc<p>
 * @author Thomas C. Hales
 * @version 1.0
 */
package graph;
import java.util.HashMap;

/**
 * The attributes of a vertex are
 *  its height and the array of faces surrounding that vertex.
 * <p>
 * There is a crude parallelism between the Vertex and Face classes, corresponding
 * to the duality of planar maps that exchanges vertices and faces.
 */
public class Vertex {
    private final int height;
    private final Face[] incidentFace;

    private Vertex(int height, int size) {
        this.height = height;
        incidentFace = new Face[size];
    }

    /**
     * This is the only public constructor.  When constructed, a vertex bounds
     * only two faces.  Vertices with higher valence can only be created through
     * faceDivision.
     * <p>
     * The height of the constructed vertex is 0.
     * <p>
     * @param F1 one bounding face around the vertex
     * @param F2 the other bounding face around the vertex.
     */

    Vertex(Face F1, Face F2, int height) {
        this.height = height;
        incidentFace = new Face[] {
            F1, F2
        };
        incidentFace[0] = F1;
        incidentFace[1] = F2;
    }

    /**
     * Make a deep clone of a vertex from another graph.

     * This method is involved.
     * Starting with a graph create a hashMap whose keys are the faces (faceDict),
     * and a hashMap whose keys are the vertices (vertexDict).  Initialize so
     * that the keys point to null.  As vertices and faces of the clone are created
     * the HashMap objects are updated with the new clone associations.
     * <p>
     * Vertices, Faces, and Graphs are immutable, so once a clone of one vertex
     * is started, the clone spreads through the entire Graph.
     * <p>
     * This method is deeply recursive and is tightly entertwined with Face.deepClone().
     * <p>
     * If reverse=true, the clone is a mirror image of the original, otherwise exact clone.
     * @param faceDict HashMap containing bindings of old faces to cloned faces
     * @param vertexDict HashMap containing bindings of od vertices to cloned vertices
     * @param reverse boolean specifying whether the clone should be a mirror image
     * <p>

     */

    Vertex deepClone(HashMap faceDict, HashMap vertexDict, boolean reverse) {
        if(vertexDict.get(this) != null)
            util.Eiffel.error("each vertex should be cloned only once");
        Vertex V = new Vertex(this.getHeight(), this.size());
        vertexDict.put(this, V);
        Face F = this.getAny();
        Face newF = null;
        for(int i = 0;i < this.size();i++) {
            F = incidentFace[i];
            newF = (Face)faceDict.get(F);
            if(newF == null)
                newF = F.deepClone(faceDict, vertexDict, reverse); // recursive;
            if(reverse)
                V.incidentFace[this.size() - i - 1] = newF;
            else
                V.incidentFace[i] = newF;
        }
        return V;
    }

    /**
     * Clone a vertex as a descendent vertex in a face division.
     * <p>
     * One face is chosen that is split into two faces.
     * The process of dividing a face is called faceDivision
     * <p>
     * See mitosis.gif
     * <p>
     *
     * @ram1 The first ramification vertex
     * @ram2 The second ramification vertex
     * @oldF The face undergoing Division.
     * @face12 The face resulting from Division from ram1 to ram2 clockwise
     * @face21 The face resulting from Division from ram2 to ram1 clockwise around oldF
     * @faceDict HashMap associating old faces with their descendents
     * @vertexDict HashMap associating old vertices with their descendents.
     * contract precondition: ram1 and ram2 are Vertices of oldF.
     * contract precondition: all arguments are non-null.
     */

    Vertex faceDivision(Vertex ram1, Vertex ram2, Face oldF, Face face12, Face face21, HashMap faceDict, HashMap vertexDict) {
        // Early exit if vertex has been processed already.
        Vertex V = (Vertex)vertexDict.get(this);
        if(V != null)
            return V;
        int distance = oldF.directedLength(ram1, ram2);
        if(distance < 0)
            util.Eiffel.error("ram1 and ram2 should lie on oldF");
        if(face12.isFinal())
            util.Eiffel.error("face12 should not be final");
        int distanceThis = oldF.directedLength(ram1, this);

         /* place new vertex in dictionary, an extra face occurs at ram1, ram2 */{
            int extra = 0;
            if(this.equals(ram1) || this.equals(ram2))
                extra++;
            V = new Vertex(this.getHeight(), this.size() + extra);
            vertexDict.put(this, V);
        }


        /* Loop through incidentFace and add corresponding Face to V
        Special cases occur if the Face is oldF */
        Face F;
        Face newF;
        int offset = 0;
        for(int i = 0;i < this.size();i++) {
            F = incidentFace[i];
            // CASE O: ram1
            if(F.equals(oldF) && distanceThis == 0) { //counterclockwise here for vertices.
                V.incidentFace[i + offset] = face21;
                offset++;
                V.incidentFace[i + offset] = face12;
            }
            // CASE 1: face12
            else
                if(F.equals(oldF) && distanceThis < distance)
                    V.incidentFace[i + offset] = face12;
                // CASE 2: ram2
                else
                    if(F.equals(oldF) && distanceThis == distance) { //counterclockwise
                        V.incidentFace[i + offset] = face12;
                        offset++;
                        V.incidentFace[i + offset] = face21;
                    }
                    // CASE 3: face21
                    else
                        if(F.equals(oldF))
                            V.incidentFace[i + offset] = face21;
                        // CASE 4: default: F!= oldF
                        else {
                            newF = (Face)faceDict.get(F);
                            if(newF == null)
                                newF = F.faceDivision(ram1, ram2, oldF, face12, face21, faceDict, vertexDict); // recursive;
                            V.incidentFace[i + offset] = newF;
                        }
        // ESAC
        }
        return V;
    }


    /**
     * Count the number of faces at the vertex that have between
     * minGon and maxGon faces (inclusive).  NonFinal faces are
     * excluded.
     * @param minGon int giving the minimum number of vertices for a face to be included in
     * the count
     * @param maxGon int giving the maximum number of vertices for a face to be included in
     * the count
     * <p>
     * Example:
     * faceCount(3,3) number of nonFinal triangles around a vertex.
     * faceCount(4,4) number of nonFinal quadrilaterals around a vertex.
     * faceCount(5,Integer.MAX_VALUE) number of nonFinal exceptional faces around a vertex.
     */

    public int faceCount(int minGon, int maxGon) {
        int count = 0;
        Face f;
        for(int i = 0;i < incidentFace.length;i++) {
            f = incidentFace[i];
            if((f.isFinal()) && (f.size() >= minGon) && (f.size() <= maxGon))
                count++;
        }
        return count;
    }

    /**
     * nonFinalCount is the number of Faces around the vertex that are not final.
     */

    public int nonFinalCount() {
        int count = 0;
        Face f;
        for(int i = 0;i < incidentFace.length;i++) {
            f = incidentFace[i];
            if(!f.isFinal())
                count++;
        }
        return count;
    }

    /**
     * The height is a field that has only minor significance.  It is
     * used heuristically in the construction of new graphs from a
     * given one.  The height is non-negative integer that roughly measures how
     * late in the construction that vertex was added.  Higher heights occur
     * in vertices that were constructed later in the game.
     * <p>
     * The height has no significance for final graphs.
     */

    public int getHeight() {
        return height;
    }

    /**
     * The size of a vertex is the number of faces with that vertex.
     */

    public int size() {
        return incidentFace.length;
    }


    /**
     * Find the count'th successor to Face f in the cyclic order around the
     * vertex.  If the Face f does not appear on the vertex, returns null.
     *
     * <p>
     * Examples:
     * next(f,0) = f;  next(f,size())=f; next(f,1) = successor, ....
     *
     * <p>
     * Face.next moves clockwise around the face, but Vertex.next moves counterclockwise.
     * This means that if faces R and S share an edge E with terminal vertices x and y,
     * and if y occurs clockwise around R from x,
     * then S=x.next(R,1); R=y.next(S,1); x=S.next(y,1); y=R.next(x,1);
     * See graphDoc.gif
     *
     * <p>
     * @param f the Face used as a base point around the Vertex.
     *
     * @param count this many faces past f to locate the Face returned.
     * The return value only depends on count mod this.size();
     */

    public Face next(Face f, int count) {
        int index = -1;
        // a bit of optimized code, using the previously found index, if possible
        if(cacheNextIndex >= 0 && cacheNextIndex < incidentFace.length && incidentFace[cacheNextIndex].equals(f))
            index = cacheNextIndex;
        else
            for(int i = 0;i < incidentFace.length;i++) {
                if(f.equals(incidentFace[i]))
                    index = i;
            }
        cacheNextIndex = index % incidentFace.length;
        if(index < 0)
            return null;
        index = (index + count) % incidentFace.length;
        if(index < 0)
            index += incidentFace.length;
        return incidentFace[index];
    }
    private int cacheNextIndex; // used for optimization in method "next"

    /**
     * getAny returns any face of the vertex.  This, together with repeated
     * calls to "next" will give an enumeration of all faces.
     * <p>
     * In the unlikely event that the vertex has no faces, a null is returned;
     */

    public Face getAny() {
        if(incidentFace.length == 0)
            return null;
        return incidentFace[0];
    }

    /**
     * Used in constructor of graph from a Formatter object.
     * @param faceIndex index of face in Formatter.vertexAtFace order
     * @param vList list of vertices being built in new graph.  Initialized to null.
     * @param fList list of faces built in new graph.
     * precondition: vList[vertexIndex]=null;
     * postcondition: vList[vertexIndex]=this;
     * postcondition: height = 0;
     */

    Vertex(Formatter f, int vertexIndex, Vertex[] vList, Face[] fList) {
        vList[vertexIndex] = this;
        height = 0;
        final int[] faceIndices = f.faceAtVertex(vertexIndex);
        incidentFace = new Face[faceIndices.length];
        for(int i = 0;i < faceIndices.length;i++) {
            int j = faceIndices[i];
            if(fList[j] == null)
                new Face(f, j, vList, fList); // warning: side-effect makes fList[j]!=null.
            incidentFace[i] = fList[j];
        }
    }
    public static class Test extends util.UnitTest {

        public void testVertex() {

        }
    }
}
