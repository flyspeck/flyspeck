/**
 * Title:        <p>
 * Description:  <p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * Company:      <p>
 * @author Thomas C. Hales
 * @version 1.0
 */
package graph;
import java.util.HashMap;

/**
 * Each Face object has two properties:
 *  1.  the vertices around the polygon, in cyclic order.
 *  2.  a boolean attribute isFinal, telling whether the face can be further modified or not.
 *
 * The attribute final is used in a way that is analogous to, but not identical
 * to, the usage in the Java language.  A final face is one that cannot undergo
 * faceDivision.
 *
 * Every graph is immutable by construction, except in its isFinal attribute,
 * but even an immutable graph is not
 * final, if it has a face that is not final.  A final graph is one that should be
 * considered as a candidate for a counterexample to the Kepler conjecture. A
 * non final graph is one that should be used to construct additional graphs.
 *
 * A face that is not final is one on which new graphs can be constructed, by
 * adding additional faces.
 *
 * A face is immutable except that the isFinal attribute can be changed through
 * the setFinal method.
 */
public class Face {
    private boolean isFinal;
    private Vertex[] incidentVertex;

    /**
     * This is the only public constructor for a face.  It creates a new face that
     * is an n-gon.  The face that is returned by the constructor has the attribute
     * isFinal set to true.  Another face is created internally that represents the
     * exterior of the polygon.  The exterior has the attribute isFinal set to false.
     * <p>
     * This constructor also constructs n-vertices, where n = size;
     * @param size the number of vertices in the face.
     * precondition: size>2
     */

    static Face getInstance(int size) {
        if(size <= 2)
            util.Eiffel.error("the parameter on Face constructor should be >2");
        Face face12 = new Face(size, true);
        Face face21 = new Face(size, false);
        Vertex v;
        for(int i = 0;i < size;i++) {
            v = new Vertex(face12, face21, 0);
            face12.incidentVertex[i] = v;
            face21.incidentVertex[size - i - 1] = v; // clockwise
        }
        return face12;
    }

    /**
     * Used by getInstance.
     * precondition: size>2
     */

    private Face(int size, boolean isFinal) {
        this.isFinal = isFinal;
        incidentVertex = new Vertex[size];
    }

    /**
     * The size of a face is the number of vertices that it has.
     */

    public int size() {
        return incidentVertex.length;
    }

    /**
     * A final Face is one that cannot be used to construct new graphs.
     */

    public boolean isFinal() {
        return isFinal;
    }

    /**
     * setFinal is the only method that violates the immutability of the
     * graph.  It is not possible to make the attribute isFinal false.
     * @param b boolean state to set isFinal to.
     */

    public void setFinal(boolean b) {
        isFinal = b;
    }

    /**
     * Make a deep copy of a Face on another graph.
     * The clone constructor is involved.
     * Starting with a graph create a hashMap whose keys are the faces (faceDict),
     * and a hashMap whose keys are the vertices (vertexDict).  Initialize so
     * that the keys point to null.  As vertices and faces of the clone are created
     * the HashMap objects are updated with the new clone associations.
     * <p>
     * Vertices, Faces, and Graphs are immutable, so once a clone of one face
     * is started, the clone spreads through the entire Graph.
     * <p>
     * This method is recursive and is tightly entertwined with Vertex.deepClone.
     * <p>
     * If reverse=true, the clone is a mirror image of the original, otherwise exact clone.
     * <p>
     * precondition: faceDict.get(this)==null;
     */

    Face deepClone(HashMap faceDict, HashMap vertexDict, boolean reverse) {
        if(faceDict.get(this) != null)
            util.Eiffel.error("duplicated face in clone");
        Face F = new Face(this.size(), this.isFinal);
        faceDict.put(this, F);
        Vertex V;
        Vertex newV;
        for(int i = 0;i < this.size();i++) {
            V = incidentVertex[i];
            newV = (Vertex)vertexDict.get(V);
            if(newV == null)
                newV = V.deepClone(faceDict, vertexDict, reverse); // recursive;
            if(reverse)
                F.incidentVertex[this.size() - i - 1] = newV;
            else
                F.incidentVertex[i] = newV;
        }
        return F;
    }

    /**
     * Treats a face that does not undergo division.
     * <p>
     * One face is chosen that is split into two faces.
     * The process of dividing a face is called faceDivision.
     * The process of faceDivision separates oldF into two faces and clones
     * all the other faces.  This method is the one called on the faces to
     * be cloned.  (A precondition for this method is that this!=oldF.)
     * <p>
     * This class is tightly coupled with the Graph constructor, and
     * other classes with "faceDivision" in the name.
     * <p>
     * Graph(..) calls initFaceDivision calls Vertex.FaceDivision calls Face.FaceDivision,
     * and Face.faceDivision calls Vertex.FaceDivision in a recursion.  No need to
     * call this directly.
     * <p>
     * See mitosis.gif
     * <p>
     *
     * @ram1 The first ramification vertex
     * @ram2 The second ramification vertex
     * @oldF The face undergoing Division.
     * @face12 The face resulting from Division from ram1 to ram2 clockwise
     * @face21 The face resulting from Division from ram2 to ram1 clockwise
     * @faceDict HashMap associating old faces with their descendents
     * @vertexDict HashMap associating old vertices with their descendents.
     * contract precondition: ram1 and ram2 are Vertices of oldF.
     * contract precondition: all arguments are non-null.
     * contract precondition: this != oldF.
     * @returns a clone of this Face.
     */

    Face faceDivision(Vertex ram1, Vertex ram2, Face oldF, Face face12, Face face21, HashMap faceDict, HashMap vertexDict) {
          /*early exit if already processed.*/{
            Face F = (Face)faceDict.get(this);
            if(F != null)
                return F;
        }

        // check preconditions:
        if(oldF.next(ram1, 0) != ram1)
            util.Eiffel.error("ram1 not on oldF");
        if(oldF.next(ram2, 0) != ram2)
            util.Eiffel.error("ram2 not on oldF");
        if(this == oldF)
            util.Eiffel.error("this should not equal oldF");
        if(face12.isFinal())
            util.Eiffel.error("face12 should not be final");
        if(face21.isFinal())
            util.Eiffel.error("face21 should not be final");
        Face F = new Face(this.size(), this.isFinal);
        faceDict.put(this, F);
        Vertex V;
        Vertex newV;
        for(int i = 0;i < this.size();i++) {
            V = incidentVertex[i];
            if(V == null)
                util.Eiffel.error("Null at " + i + " " + this.size());
            newV = (Vertex)vertexDict.get(V);
            if(newV == null)
                newV = V.faceDivision(ram1, ram2, oldF, face12, face21, faceDict, vertexDict); // recursive;
            F.incidentVertex[i] = newV;
        }
        return F;
    }

    /**
     * Treats the face undergoing division
     * @ram1 first ramification vertex (see mitosis.gif)
     * @ram2 second ramification vertex
     * @this Face undergoing Division
     * @newVertexCount number of vertices to add in Division
     * @faceDict association of old faces to new
     * @vertexDict association of old vertices to new
     * @return an array of newly created vertices, ordered from ram1 to ram2.
     * <p>
     * precondition: ram1!=ram2, ram1 and ram2 are vertices on this.
     * postcondition: the length of the returned array = newVertexCount.
     * postcondition: the faceDict has increased in length by two adding the two keys
     *    face12Key -> face12,
     *    face21Key -> face21
     * postcondition: The face12 runs clockwise from ram1 to ram2
     * <p>
     * Through recursive calls to Face.faceDivision Vertex.faceDivision, the entire
     *  structure is created and the faceDict and vertexDict are updated with keys
     *    Face in ancester -> Face in descendant
     *    Vertex in ancester -> Vertex in descendant
     * <p>
     * postcondition: this -> null. That is, the faceDict is never updated on the
     *  face undergoing division.  That information is stored instead under the keys
     *  face12Key and face21Key.
     */

    Vertex[] initFaceDivision(Vertex ram1, Vertex ram2, int newVertexCount, Object face12Key, Object face21Key, HashMap faceDict, HashMap vertexDict) {
        //1. check preconditions:
        if(ram1.equals(ram2))
            util.Eiffel.error("ram1 should not equal ram2");
        if(next(ram1, 0) != ram1)
            util.Eiffel.error("ram1 should lie on this Face");
        if(next(ram2, 0) != ram2)
            util.Eiffel.error("ram2 should lie on this Face");
        //2. create the new Faces:
        int distance = directedLength(ram1, ram2);
        Face face12 = new Face(distance + 1 + newVertexCount, false);
        Face face21 = new Face(1 + newVertexCount + size() - distance, false);
        faceDict.put(face12Key, face12);
        faceDict.put(face21Key, face21);
        //3. create the new Vertices
        Vertex[] newV = new Vertex[newVertexCount];
        Vertex V;
        for(int i = 0;i < newVertexCount;i++) {
            V = new Vertex(face12, face21, Math.min(ram2.getHeight() + i + 1, ram1.getHeight() + newVertexCount - i));
            newV[newVertexCount - 1 - i] = V;
            face12.incidentVertex[i] = V; // clockwise around face12
            face21.incidentVertex[face21.size() - 1 - i] = V; // index> size()-distance
        }
        //4. add the vertices to the final face (with recursion)
        for(int i = 0;i < distance + 1;i++) { // +1 to include both ram1 and ram2
            face12.incidentVertex[newVertexCount + i] = next(ram1, i).faceDivision(ram1, ram2, this, face12, face21, faceDict, vertexDict);
        }
        //5. add the vertices to the nonfinal face (with recursion)
        for(int i = 0;i < size() + 1 - distance;i++) { // +1 to include both ram2 and ram1
            face21.incidentVertex[i] = /* top index is size-distance.*/ next(ram2, i).faceDivision(ram1, ram2, this, face12, face21, faceDict, vertexDict);
        }
        return newV;
    }



    /**
     * Find the count'th successor to vertex v in the cyclic order around the
     * face.  If the Vertex v does not appear on the Face, returns null.
     *
     * <p>
     * Examples:
     * next(v,0) = v;  next(v,size())=v; next(v,1) = successor in a clockwise direction.
     *
     * <p>
     * Face.next moves clockwise around the face, but Vertex.next moves counterclockwise.
     * This means that if faces R and S share an edge E with terminal vertices x and y,
     * and if y occurs clockwise around R from x,
     * then S=x.next(R,1); R=y.next(S,1); x=S.next(y,1); y=R.next(x,1);
     * See graphDoc.gif
     *
     * <p>
     * @param v the Vertex used as a base point along the Face.  If v
     * does not appear on the Face, return null.
     *
     * @param count this many vertices past v to locate the Vertex returned.
     * The return value only depends on count mod this.size();
     *
     * <p>
     */

    public Vertex next(Vertex v, int count) {
        int index = -1;
        // a bit of optimized code that uses cachedIndex if possible
        if(cachedIndex >= 0 && cachedIndex < incidentVertex.length && incidentVertex[cachedIndex].equals(v))
            index = cachedIndex;
        else
            for(int i = 0;i < incidentVertex.length;i++) {
                if(incidentVertex[i].equals(v))
                    index = i;
            }
        cachedIndex = index;
        if(index < 0)
            return null;
        index = (index + count) % incidentVertex.length;
        if(index < 0)
            index += incidentVertex.length; // % has sign of first arg
        return incidentVertex[index];
    }
    private int cachedIndex;

    /**
     * getAny returns any vertex of the face.  This, together with repeated
     * calls to "next" will give an enumeration of all vertices.
     * <p>
     * In the unlikely event that the Face has no vertices, a null is returned;
     */

    public Vertex getAny() {
        if(incidentVertex.length == 0)
            return null;
        return incidentVertex[0];
    }

    /**
     * The number of edges along this Face from v1 to v2, moving in clockwise
     * direction.
     * <p>
     * Invariant: If r=directedLength(v1,v2), then next(v1,r) equals v2;
     * @param v1 The first vertex on this Face.
     * @param v2 The second vertex on this Face.
     * @return -1 if v1 or v2 is not on this Face, else a nonnegative integer.
     */

    public int directedLength(Vertex v1, Vertex v2) {
        int v1Index = -1, v2Index = -1;
        for(int i = 0;i < incidentVertex.length;i++) {
            if(incidentVertex[i].equals(v1))
                v1Index = i;
            if(incidentVertex[i].equals(v2))
                v2Index = i;
        }
        if(v1Index < 0 || v2Index < 0)
            return -1;
        return Misc.mod(v2Index - v1Index, incidentVertex.length);
    }

    /**
     * Used in constructor of graph from a Formatter object.
     * @param faceIndex index of face in Formatter.vertexAtFace order
     * @param vList list of vertices being built in new graph.  Initialized to null.
     * @param fList list of faces built in new graph.
     * precondition: fList[faceIndex]=null;
     * postcondition: fList[faceIndex]=this;
     * Recursive calls to Vertex constructor, so that entire graph gets constructed at once.
     */

    Face(Formatter f, int faceIndex, Vertex[] vList, Face[] fList) {
        fList[faceIndex] = this;
        final int[] vertexIndices = f.vertexAtFace(faceIndex);
        isFinal = f.isFinal(faceIndex);
        incidentVertex = new Vertex[vertexIndices.length];
        for(int i = 0;i < vertexIndices.length;i++) {
            int j = vertexIndices[i];
            if(vList[j] == null)
                new Vertex(f, j, vList, fList); // warning: side-effect makes vList[j]!=null
            incidentVertex[i] = vList[j];
        }
    }


    /**
     * Unit util of Face
     *
     */
    public static class Test extends util.UnitTest {

        public void testGetInstance() {
            for(int N = 3;N < 6;N++) {
                Face F = Face.getInstance(N);
                testPolygon(F, N);
            }
        }

        private void testPolygon(Face F, int N) {
            jassert(F.size() == N);
            Vertex v = F.getAny();
            jassert(v.size() == 2);
            Vertex[] vA = new Vertex[N];
            for(int i = 0;i < N;i++)
                vA[i] = F.next(v, i);
            jassert(v.equals(F.next(v, 0)));
            jassert(v.equals(F.next(v, N)));
            jassert(F.isFinal);
            Face F2 = v.next(F, 1);
            jassert(v.next(F, 2).equals(F));
            jassert(v.next(F2, 2).equals(F2));
            jassert(!F2.isFinal);
            jassert(v.faceCount(3, N) == 1);
            jassert(v.faceCount(N, N) == 1);
            jassert(v.nonFinalCount() == 1);
            F2.setFinal(true);
            jassert(v.nonFinalCount() == 0);
            jassert(v.faceCount(N, N) == 2);
            jassert(F2.isFinal);
            for(int i = 0;i < N;i++)
                jassert(F2.next(v, -i).equals(vA[i]));
            for(int i = 0;i < N;i++)
                for(int j = 0;j < N;j++)
                    if(i != j)
                        jassert(vA[i] != vA[j]);
            for(int i = 0;i < N;i++)
                jassert(F.directedLength(v, vA[i]) == i);
        }

        public void testDeepClone() {
            int N = 5;
            for(int j = 0;j < 2;j++) {
                Face F = getInstance(N);
                HashMap faceDict = new HashMap();
                HashMap vertexDict = new HashMap();
                Vertex v = F.getAny();
                for(int i = 0;i < 2;i++)
                    faceDict.put(v.next(F, i), null);
                for(int i = 0;i < N;i++)
                    vertexDict.put(F.next(v, i), null);
                Face clone = F.deepClone(faceDict, vertexDict, (j > 0));
                testPolygon(clone, N);
            }
        }
    }
}
