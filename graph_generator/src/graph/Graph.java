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
import java.util.HashMap;
import java.util.HashSet;

/**
 * A Graph object represents a planar graph (or better, map).
 * The data structures stores a list of vertices and faces.
 * The vertices know about the faces around them, and vice versa.
 * The edge structure is determined by the relationship of vertices and faces.
 * <p>
 * Rather than loading this class with tons of structural information, we
 * implement things roughly on a Model-Controller-Viewer design pattern.
 * The Graph Class is the Model for the data, and constructors contain the controller code.
 * The various viewers take different structural views of this class
 *  (View scores, view structures, format conversions, etc).
 * All controller code lies in the constructors, because the Graph Class is immutable.
 * <p>
 * The purpose of this code is to prove part of the Kepler conjecture.  Specifically:
 *    1. Give a fresh implementation of the graph package at
 *          www.math.lsa.umich.edu/~hales/countdown/graph.
 *    2. Give a useful data structure for use in the linear programming part of
 *          the Kepler conjecture
 * <p>
 *
 */
public class Graph {
    private final Vertex[] vertexList; // order is not of instrinsic significance.
    private final Face[] faceList; // order is that in which the faces were constructed.

    public boolean contains(Vertex V) {
        for(int i = 0;i < vertexList.length;i++)
            if(V == vertexList[i])
                return true;
        return false;
    }

    public boolean contains(Face F) {
        for(int i = 0;i < faceList.length;i++)
            if(F == faceList[i])
                return true;
        return false;
    }

    /**
     * When there are no exceptionals the baseVertex=null;
     * When there are exceptionals, let F be a function that selects one vertex from
     * each completed graph in such a way that this vertex lies on a face of maximal size.
     * (The rule we use is F(G) = any vertex with maximal Score.hashVertex().)
     * Then we considered graphs (G,F(G)) with a base point.
     * As we generate graphs, we may assume that we used for seed a face with the maximal
     * number of sides containing the base point.
     */
    private Vertex baseVertex = null;

    public Vertex getBaseVertex() {
        return baseVertex;
    }

    protected void setBaseVertex(Vertex V) {
        baseVertex = V;
    }


    /**
     * The number of vertices in the graph.
     */

    public int vertexSize() {
        return vertexList.length;
    }

    /**
     * The number of faces in the graph
     */

    public int faceSize() {
        return faceList.length;
    }

    /**
     * Enumerates all Vertex objects.  The order
     * has no intrinsice significance, but it is preserved
     * under cloning and mirror images.
     * Objects may be safely cast to Vertex.
     */

    public Enumeration vertexEnumeration() {
        return new Enumeration()  {
            int i = 0;

            public boolean hasMoreElements() {
                return i < vertexList.length;
            }

            public Object nextElement() {
                return vertexList[i++];
            }
        };
    }

    /**
     * Enumerates all Face objects.  The order
     * is preserved under cloning and mirror images.
     * Under faceDivision, one face (face21) keeps the order of the parent,
     * and the other
     * is added to the end of the Enumeration.
     * Objects can be safely cast to (Face).
     */

    public Enumeration faceEnumeration() {
        return new Enumeration()  {
            int i = 0;

            public boolean hasMoreElements() {
                return i < faceList.length;
            }

            public Object nextElement() {
                return faceList[i++];
            }
        };
    }
    /**
     * Construct a polygon graph.
     * @param size the number of vertices in the polygon.
     * @post two faces, one final and the other not, same vertices.
     * @post baseVertex a random vertex on the polygon.
     * @post heights of the vertices are zero.
     */

    public static Graph getInstance(int size) {
        return new Graph(size);
    }

    private Graph(int size) {
        vertexList = new Vertex[size];
        faceList = new Face[2];
        Face F = Face.getInstance(size);
        util.Eiffel.jassert(F.isFinal());
        Vertex v = F.getAny();
        for(int i = 0;i < size;i++)
            vertexList[i] = F.next(v, i);
        for(int i = 0;i < 2;i++)
            faceList[i] = v.next(F, i);
        baseVertex = v;
    }

    /**
     * Construct a graph from a formatter object. The enumeration order is preserved.
     */

    public static Graph getInstance(Formatter f) {
        return new Graph(f);
    }

    private Graph(Formatter f) {
        faceList = new Face[f.faceCount()];
        vertexList = new Vertex[f.vertexCount()];
        new Face(f, 0, vertexList, faceList); // all initialization done recursively.
    }


    /**
     * deepClone or deepMirrorImage of the graph.
     * @param G graph to clone
     * @param vList any array of Vertices on G,
     * @post  vList clones of the initial array.
     * @param fList any array of Faces on G.
     * @post  fList clones of the initial array.
     * @param reverse if true, a mirror image of G is constructed.
     * @invariant Graph constructed is independent of vList fList
     * @invariant the order of faceEnumeration and vertexEnumeration is preserved
     * @invariant baseVertex and Face.isFinal are preserved.
     */

    public Graph copy(boolean reverse, Vertex[] vList, Face[] fList) {
        return new Graph(this, reverse, vList, fList);
    }

    private Graph(Graph G, boolean reverse, Vertex[] vList, Face[] fList) {
        HashMap vertexDict = new HashMap(G.vertexList.length);
        HashMap faceDict = new HashMap(G.faceList.length);
        for(int i = 0;i < G.vertexList.length;i++)
            vertexDict.put(G.vertexList[i], null);
        for(int i = 0;i < G.faceList.length;i++)
            faceDict.put(G.faceList[i], null);
        Face F = G.faceList[0];
        F.deepClone(faceDict, vertexDict, reverse); // recursively creates faceDict & vertexDict
        // set baseVertex
        baseVertex = (Vertex)vertexDict.get(G.baseVertex);
        // update lists and return.
        faceList = new Face[G.faceList.length];
        vertexList = new Vertex[G.vertexList.length];
        for(int i = 0;i < faceList.length;i++) {
            faceList[i] = (Face)faceDict.get(G.faceList[i]);
            util.Eiffel.jassert(faceList[i] != null);
        }
        for(int i = 0;i < vertexList.length;i++) {
            vertexList[i] = (Vertex)vertexDict.get(G.vertexList[i]);
            util.Eiffel.jassert(vertexList[i] != null);
        }
        for(int i = 0;i < vList.length;i++)
            vList[i] = (Vertex)vertexDict.get(vList[i]);
        for(int i = 0;i < fList.length;i++)
            fList[i] = (Face)faceDict.get(fList[i]);
    }

    /**
     * Shallow clone of graph.
     */
    protected Graph(Graph G) {
      this.baseVertex = G.baseVertex;
      this.vertexList = G.vertexList;
      this.faceList = G.faceList;
    }


    /**
     * helper for Graph constructor
     * counts number of nulls following first V in list.
     * @pre V lies in list.
     */

    private int nullCount(Vertex V, Vertex[] list) {
        int index = -1;
        util.Eiffel.precondition(V != null && list != null);
        for(int i = 0;i < list.length;i++)
            if(list[i] == V) {
                index = i;
                break;
            }
        util.Eiffel.jassert(index != -1);
        int count = 0;
        while(null == list[Misc.mod(index + 1 + count, list.length)])
            count++;
        return count;
    }

    /**
     * Graph with one new polygon added along an edge.
     * <p>
     * @param F list of length 1 containing the Face to be modified.
     * @post F, replaced by image in new Graph, vertices newFaceVertexList.
     * @post F[0] isFinal=true; other faces created as byproduct isFinal=false;
     * @param newFaceVertexList, all vertices cyclically arranged (clockwise), nulls for new Vertices.
     * @post newFaceVertexList replaced by image in the new Graph.
     * <p>
     * Example: add a triangle along Face F, along edge (V,W) with one new vertex.
     * G.add(new Face[] {F},new Vertex[] {V,null,W}); // {V,null,W} must be clockwise.
     */

    public Graph add(Face[] F, Vertex[] newFaceVertexList) {
        return new Graph(this, F, newFaceVertexList);
    }

    private Graph(Graph G, Face[] F, Vertex[] newFaceVertexList) {
        //0. preconditions:
        util.Eiffel.precondition(F != null && F.length == 1 && !F[0].isFinal(), " " + (F != null) + " " + F.length);
        util.Eiffel.precondition(newFaceVertexList != null & newFaceVertexList.length > 2);
        int constructcount = 0;
        while(true) { //infinite loop.
            //1. search for starting point: Vertex followed by a null or a non-adjacent edge.
            int index = -1;
            for(int i = 0;i < newFaceVertexList.length;i++) {
                Vertex V1 = newFaceVertexList[i];
                Vertex V2 = newFaceVertexList[Misc.mod(i + 1, newFaceVertexList.length)];
                if(V1 != null && V2 == null) {
                    index = i;
                    break;
                }
                if(V1 != null && V2 != null && F[0].next(V1, 1) != V2) {
                    index = i;
                    break;
                }
            }
            //2. if all were null or if all were adjacent, then wrap up.
            if(index < 0) {
                if(constructcount == 0)
                    G = new Graph(G, false, newFaceVertexList, F);
                break; // break; out of infinite loop here.
            }
            //3. construct an edge
            Vertex firstRam = newFaceVertexList[index];
            util.Eiffel.jassert(firstRam != null);
            int newVertexCount = nullCount(firstRam, newFaceVertexList);
            Vertex secondRam = newFaceVertexList[Misc.mod(1 + newVertexCount + index, newFaceVertexList.length)];
            constructcount++;
            Vertex[] newV = new Vertex[newVertexCount];
            Face[] split = new Face[2];
            G = new Graph(G, firstRam, secondRam, F[0], split, newV, newFaceVertexList, F);
            util.Eiffel.jassert(testDistinctVertices(split[0]));
            util.Eiffel.jassert(testDistinctVertices(split[1]));
            util.Eiffel.jassert(F[0]==split[1]);
            //4. update newFaceVertexList with newly created vertices.
            for(int i = 0;i < newVertexCount;i++)
                newFaceVertexList[Misc.mod(index + i + 1, newFaceVertexList.length)] = newV[i];
        }
        F[0].setFinal(true);
        faceList = G.faceList;
        vertexList = G.vertexList;
        baseVertex = G.baseVertex;
    }

    /**
     * For debugging purposes. Check that vertices of F are distinct.
     */
    private boolean testDistinctVertices(Face F) {
        util.Eiffel.precondition(F!=null);
        Vertex V = F.getAny();
        HashSet S = new HashSet();
        for (int i=0;i<F.size();i++) {
            Vertex W = F.next(V,i);
            if (S.contains(W))
                return false;
            S.add(W);
        }
        return true;
    }

    /**
     * Construct graph from seedData giving a graph around one vertex.
     * See graphConstruct.gif
     * @param seedData a clockwise array of integers specifying sizes of consecutive faces.
     * @post faces around central vertex have isFinal true, face "at infinity" isFinal=false;
     * @post baseVertex==null;
     */

    public static Graph getInstance(int[] seedData) {
        return new Graph(seedData);
    }

    private Graph(int[] seedData) {
        //0. preconditions
        util.Eiffel.precondition(seedData != null && seedData.length > 1);
        //1. Add the first face.
        Graph G = new Graph(seedData[0]);
        Vertex V = G.vertexList[0];
        Face F = V.getAny();
        if(F.isFinal())
            F = V.next(F, 1);
        if(F.isFinal())
            util.Eiffel.error("Graph should have face21");
        //2. Add all but the last face.
        for(int i = 1;i < seedData.length - 1;i++) {
            Vertex[] vList = new Vertex[] {
                V
            };
            Face[] fList = new Face[] {
                F
            };
            G = new Graph(G, V, F.next(V, 1), F, new Face[2], new Vertex[seedData[i] - 2], vList, fList); // 2 vertices attached.
            V = vList[0];
            F = fList[0];
            V.next(F, 1).setFinal(true);
        }
        //3. Add the last face (-3 because 3 vertices are attached).
        Face[] splitF = new Face[] {null,null};
        G = new Graph(G, F.next(V, -1), F.next(V, 1), F, splitF, new Vertex[seedData[seedData.length - 1] - 3], new Vertex[0], new Face[0]);
        splitF[0].setFinal(true);
        vertexList = G.vertexList;
        faceList = G.faceList;
    }

    /**
     * Construct a new Graph by faceDivision of face F in G.
     * @param G ancester graph.
     * @param ram1 first ramification vertex, vertex at which new edge joins to F.
     * @param ram2 second ramification vertex, vertex at which new edge joins to F.
     * @notation face12 face created with boundary from ram1 to ram2 clockwise along F.
     * @notation face21 face created with boundary from ram2 to ram1 clockwise along F
     * @param splitFace write-only parameter with output {face12,face21};
     * @param newVertexList write-only parameter with output new vertices, ordered from ram1 to ram2.
     * @param newVertexList.length number of new vertices to add to the graph.
     * @param vList any array of Vertices in G.
     * @post vList the image in the new graph of the input vertices.
     * @param fList any array of Faces in G.
     * @post fList the image in the new graph of the input faces.
     * @invariant The constructed graph does not depend on vList and fList.
     * @invariant The image of oldF is by convention face21, rather than face12.
     * <p>
     * See mitosis.gif, Vertex.faceDivision, Face.faceDivision
     * There is tight coupling among this constructor and Vertex.faceDivision, Face.faceDivision,
     * and Face.initFaceDivision.
     * @pre if newVertexList.length==0, then ram1 and ram2 are not adjacent along F.
     */

    protected Graph(Graph G, Vertex ram1, Vertex ram2, Face oldF, Face[] splitFace, Vertex[] newVertexList, Vertex[] vList, Face[] fList) {
        //0. check preconditions:
        util.Eiffel.precondition(fList != null && vList != null && newVertexList != null);
        util.Eiffel.precondition(splitFace != null && splitFace.length == 2);
        util.Eiffel.precondition(!oldF.isFinal());
          /*--*/{
            boolean found = false;
            for(int i = 0;i < G.faceList.length;i++)
                if(oldF == G.faceList[i])
                    found = true;
            util.Eiffel.precondition(found);
        }
        util.Eiffel.precondition(oldF.directedLength(ram1, ram2) > 0);
        if(newVertexList.length == 0)
            util.Eiffel.precondition(oldF.directedLength(ram1, ram2) != 1 && oldF.directedLength(ram2, ram1) != 1);

        //1. init vertexDict
        int newVertexCount = newVertexList.length;
        HashMap vertexDict = new HashMap(G.vertexList.length);
        for(int i = 0;i < G.vertexList.length;i++)
            vertexDict.put(G.vertexList[i], null);

        //2. init faceDict
        HashMap faceDict = new HashMap(G.faceList.length);
        for(int i = 0;i < G.faceList.length;i++)
            faceDict.put(G.faceList[i], null);

        //3. create special keys for face12 and face21, construct the face division.
        Object face12Key = new Object();
        Object face21Key = new Object();
        Vertex[] newList = oldF.initFaceDivision(ram1, ram2, newVertexCount, face12Key, face21Key, faceDict, vertexDict);
        if(faceDict.get(face12Key) == null)
            util.Eiffel.error("face12Key error");
        if(faceDict.get(face21Key) == null)
            util.Eiffel.error("face21Key error");
        if(newList.length != newVertexList.length)
            util.Eiffel.error("length mismatch");
        for(int i = 0;i < newList.length;i++)
            newVertexList[i] = newList[i];

        //4. set vertex list.
        vertexList = new Vertex[newVertexCount + G.vertexList.length];
        for(int i = 0;i < G.vertexList.length;i++)
            vertexList[i] = (Vertex)vertexDict.get(G.vertexList[i]);
        for(int i = 0;i < newList.length;i++)
            vertexList[i + G.vertexList.length] = newList[i];
        for(int i = 0;i < vertexList.length;i++)
            util.Eiffel.jassert(vertexList[i] != null);

        //5. set baseVertex
        baseVertex = (Vertex)vertexDict.get(G.baseVertex);

        //6. set face list.
        faceList = new Face[G.faceList.length + 1];
        int j = 0;
        Face F;
        for(int i = 0;i < G.faceList.length;i++) {
            F = (Face)faceDict.get(G.faceList[i]);
            if(G.faceList[i] != oldF) {
                faceList[i] = (Face)faceDict.get(G.faceList[i]);
                if(G.faceList[i] == null)
                    util.Eiffel.error("unexpected null");
            }
            else
                faceList[i] = (Face)faceDict.get(face21Key);
        }
        faceList[G.faceList.length] = (Face)faceDict.get(face12Key);
        for(int i = 0;i < faceList.length;i++)
            if(faceList[i] == null)
                util.Eiffel.error("null faceList item " + i + " " + faceList.length);

        //7. update splitFace, vList, and fList;
        splitFace[0] = (Face)faceDict.get(face12Key);
        splitFace[1] = (Face)faceDict.get(face21Key);
        for(int i = 0;i < vList.length;i++)
            vList[i] = (Vertex)vertexDict.get(vList[i]);
        for(int i = 0;i < fList.length;i++) {
            if(fList[i] == oldF)
                fList[i] = (Face)faceDict.get(face21Key);
            else
                fList[i] = (Face)faceDict.get(fList[i]);
        }
    }

    /**
     * Test Class contains test code.
     */
    public static class Test extends util.UnitTest {

        public void testGraphConstructorSize() {
            Graph G = new Graph(5);
            jassert(G.vertexList.length == 5);
            jassert(G.faceList.length == 2);
            Face F1 = G.faceList[0];
            Face F2 = G.faceList[1];
            jassert(F1.isFinal() || F2.isFinal());
            jassert(!F1.isFinal() || !F2.isFinal());
            Vertex V = F1.getAny();
            for(int i = 0;i < 5;i++)
                jassert(F1.next(V, i) == F2.next(V, -i));
            for(int i = 0;i < 5;i++)
                jassert(F1.next(V, i).next(F1, 1) == F2);
            for(int i = 0;i < 5;i++)
                jassert(F1.next(V, i).next(F2, 1) == F1);
            for(int i = 0;i < 2;i++)
                jassert(G.faceList[i] != null);
            for(int i = 0;i < 5;i++)
                jassert(G.vertexList[i] != null);
        }

        public void testGraphSeedData() {
            Graph G = new Graph(new int[] {
                6, 5, 4, 3
            }); // see GraphConstruct.gif
            Face F = G.faceList[0];
            Vertex V = F.getAny();
            while(!F.isFinal())
                F = V.next(F, 1);
            while(V.size() < 4)
                V = F.next(V, 1);
            jassert(V.size() == 4);
            while(F.size() < 6)
                F = V.next(F, 1);
            jassert(F.size() == 6);
            Face[] Flist = new Face[4];
            for(int i = 0;i < 4;i++)
                Flist[i] = V.next(F, -i);
            for(int i = 0;i < 4;i++)
                jassert(Flist[i].size() == 6 - i);
        }
    }
}
