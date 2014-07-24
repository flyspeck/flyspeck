package graph;
import java.util.StringTokenizer;
import java.util.Enumeration;

/**
 * Example of a string archive format S of a graph with 23 faces.
 * " 0 //first group
 *   23 //main group
 *    5 4 5 11 14 10 //1
 *    3 4 10 9
 *    3 9 10 14
 *    3 9 14 13
 *    3 13 14 11    //5
 *    3 13 11 12
 *    3 12 11 6
 *    3 6 11 5
 *    3 6 5 1
 *    3 1 5 0      //10
 *    3 0 5 4
 *    3 0 4 3
 *    3 3 4 9
 *    4 3 9 13 8
 *    3 8 13 12    //15
 *    3 8 12 7
 *    3 7 12 6
 *    3 7 6 1
 *    3 7 1 2
 *    3 2 1 0     //20
 *    3 2 0 3
 *    3 2 3 8
 *    3 8 7 2"    //23
 */

/**
 * format of graph*.java:
 * first integer is the number of temp faces if this is positive, else it is the hash code of the graph.
 * first group is (1+n) elements, where n is the first element.
 * n = number of temporary faces, followed by the facenumber of each temp.
 * the main group follows next m+f1+f2+...fm
 * m = number of faces total, followed by data fi for each face.
 * fi = (1+li) elements, li is the constant in the first element,
 * it is the number of vertices on the polygon,
 * followed by the vertex numbers of each element,
 * listed in clockwise order around the face.
 **/

/**
 * This class handles conversions of graphs to various formats.
 * Graph -> archiveString <-> Formatter -> MathematicaString.
 * There is also a constructor Graph(Formatter f);
 * <p>
 * The internal arrays store graph incidence data for a planar.

 * The tempList is a list of face numbers of the faces that are temporary.
 *
 * This code for this class was adapted from java98.GraphArrays.
 *
 **/
public class Formatter {
    // vertexAtFace is a list of lists of vertices vertexAtFace[0]={v1,v2,v3,..,vn} firstface vertices
    private int vertexAtFace[][]; // vertexAtFace[i]= vertices around face i (clockwise)
    private int adjacent[][]; // adjacent[i] = vertices around vertex i (counterclockwise)
    private int faceAtVertex[][]; // faceAtVertex[i] = faces around vertex i (counterclockwise)
    private int tempList[]; // tempList[i] = facenumber of ith temp face.

    public int adjacentSize(int i) {
        return adjacent[i].length;
    }

    public int adjacent(int i, int index) {
        return adjacent[i][index];
    }

    public boolean isFinal(int faceIndex) {
        for(int i = 0;i < tempList.length;i++) {
            if(tempList[i] == faceIndex)
                return false;
        }
        return true;
    }

    public int tempCount() {
        return tempList.length;
    }

    public final int[] tempList() {
        return tempList;
    }

    public final int[] vertexAtFace(int faceIndex) {
        return vertexAtFace[faceIndex];
    }

    public final int[] faceAtVertex(int vertexIndex) {
        return faceAtVertex[vertexIndex];
    }

    public int faceCount() {
        return vertexAtFace.length;
    }

    public int faceCount(int vertexIndex) {
        return faceAtVertex[vertexIndex].length;
    }

    public int vertexCount() {
        return faceAtVertex.length;
    }

    public int vertexCount(int faceIndex) {
        return vertexAtFace[faceIndex].length;
    }

    /**
     * Conversion from Formatter to archive string format.
     */

    public String toArchiveString() {
        StringBuffer B = new StringBuffer();
        B.append(tempList.length + " ");
        for(int i = 0;i < tempList.length;i++)
            B.append(tempList[i] + " ");
        B.append(vertexAtFace.length + " ");
        for(int i = 0;i < vertexAtFace.length;i++) {
            B.append(vertexAtFace[i].length + " ");
            for(int j = 0;j < vertexAtFace[i].length;j++)
                B.append(vertexAtFace[i][j] + " ");
        }
        return B.toString();
    }

    /** Constructor
     * @param S archive format string representing a graph.
     */

    public Formatter(String S) {
        //1. tokenize string
        StringTokenizer Token = new StringTokenizer(S);
        int L = Token.countTokens();
        int tokarray[] = new int[L];
        int i, j;
	//1bis. skip over first token.
	tokarray[0]=0; 
	Token.nextToken();
        for(i = 1;i < L;i++)
            tokarray[i] = Integer.valueOf(Token.nextToken()).intValue();
        //2. Set temp list;
        int offset = 0;
        tempList = new int[tokarray[0]];
        offset = 1;
        for(i = 0;i < tempList.length;i++)
            tempList[i] = tokarray[offset + i];
        offset += tokarray[0];
        //3. Set face list;
        vertexAtFace = new int[tokarray[offset]][];
        offset++;
        for(i = 0;i < vertexAtFace.length;i++) {
            vertexAtFace[i] = new int[tokarray[offset]];
            offset++;
            for(j = 0;j < vertexAtFace[i].length;j++)
                vertexAtFace[i][j] = tokarray[offset + j];
            offset += vertexAtFace[i].length;
        }
        //4. adjacentCount is the number of vertices:
        int adjacentCount = -1;
        for(i = 0;i < vertexAtFace.length;i++) {
            for(j = 0;j < vertexAtFace[i].length;j++) {
                if(vertexAtFace[i][j] > adjacentCount)
                    adjacentCount = vertexAtFace[i][j];
            }
        }
        adjacentCount++;
        //5. adjacentSizes[i] is the number of faces at vertex i.
        adjacent = new int[adjacentCount][];
        faceAtVertex = new int[adjacentCount][];
        int adjacentSizes[] = new int[adjacentCount];
        for(i = 0;i < adjacentCount;i++)
            adjacentSizes[i] = 0;
        for(i = 0;i < vertexAtFace.length;i++) {
            for(j = 0;j < vertexAtFace[i].length;j++)
                adjacentSizes[vertexAtFace[i][j]]++;
        }
        for(i = 0;i < adjacentCount;i++) {
            adjacent[i] = new int[adjacentSizes[i]];
            faceAtVertex[i] = new int[adjacentSizes[i]];
        }
        //6. For each vertex and face of vertex, d is a triple.
        // For each vertex triple[0]=counterclock vertex, triple[1]=clockwise v, triple[2]=face#
        int d[][][] = new int[adjacentCount][][];
        int len[] = new int[adjacentCount];
        for(i = 0;i < adjacentCount;i++)
            len[i] = 0;
        //7. i1,i2,i3 consecutive clockwise around face vertexAtFace[i];
        int i1, i2, i3, r;
        for(i = 0;i < adjacentCount;i++)
            d[i] = new int[adjacentSizes[i]][3];
        for(i = 0;i < vertexAtFace.length;i++) {
            for(j = 0;j < vertexAtFace[i].length;j++) {
                r = vertexAtFace[i].length;
                i1 = vertexAtFace[i][j % r];
                i2 = vertexAtFace[i][(j + 1) % r];
                i3 = vertexAtFace[i][(j + 2) % r];
                d[i2][len[i2]][0] = i1;
                d[i2][len[i2]][1] = i3;
                d[i2][len[i2]][2] = i; // face ID.
                len[i2]++;
            }
        }
        //8. now sort;
        for(i = 0;i < adjacentCount;i++) {
            for(r = 0;r + 1 < adjacentSizes[i];r++) {
                for(j = 0;j < len[i];j++) {
                    if(d[i][r][1] == d[i][j][0]) {
                        int[] swap;
                        swap = d[i][j];
                        d[i][j] = d[i][r + 1];
                        d[i][r + 1] = swap;
                    }
                }
            }
        }
        //9. now initialize adjacent
        for(i = 0;i < adjacentCount;i++) {
            for(j = 0;j < adjacentSizes[i];j++) {
                adjacent[i][j] = d[i][j][0];
                faceAtVertex[i][j] = d[i][j][2];
            }
        }
    }

    /**
     * helper function for toArchiveString(graph G);
     * @param faceAtVertex
     */

    private static String faceToString(Vertex[] vList, Face F) {
        StringBuffer S = new StringBuffer();
        S.append(F.size() + " ");
        Vertex V = F.getAny();
        for(int i = 0;i < F.size();i++) {
            Vertex W = F.next(V, i);
            for(int j = 0;j < vList.length;j++) {
                if(vList[j].equals(W))
                    S.append(j + " ");
            }
        }
        return S.toString();
    }

    /**
     * Convert a graph into archive string format.
     * @param G graph to be converted.
     * To convert back, use two steps:
     * toGraph(new Formatter(archiveString));
     */

    public static String toArchiveString(Graph G) {
        Invariant inv = new Invariant(G);
        int numTemp = 0;
        StringBuffer pre = new StringBuffer();
        StringBuffer S = new StringBuffer();
        // make an array of all faces.
        Face[] faceList = new Face[G.faceSize()];
        int index = 0;
        for (Enumeration E = G.faceEnumeration();E.hasMoreElements();/*--*/) {
            faceList[index++] = (Face)E.nextElement();
        }
        // array of vertices
        Vertex[] vertexList = new Vertex[G.vertexSize()];
        index = 0;
        for (Enumeration E= G.vertexEnumeration();E.hasMoreElements();/*--*/) {
            vertexList[index++] = (Vertex)E.nextElement();
        }
        //
        for(int i = 0;i < G.faceSize();i++) {
            Face F = faceList[i];
            if(!F.isFinal()) {
                numTemp++;
                pre.append(i + " ");
            }
            S = S.append(faceToString(vertexList, F));
        }
	long r = (numTemp>0 ? numTemp : inv.getHash());
        return "" + r + " " + pre + G.faceSize() + " " + S.toString();
    }

    /**
     * helper method for toMathematicaString.
     * @param vIndex of a vertex.
     */

    private String ptString(int vIndex) {
        int triCount = 0;
        int quadCount = 0;
        int exCount = 0;
        for(int i = 0;i < faceAtVertex[vIndex].length;i++) {
            switch(vertexAtFace[faceAtVertex[vIndex][i]].length) {
                case 3:
                    triCount++;
                    break;

                case 4:
                    quadCount++;
                    break;

                default:
                    exCount++;
            }
        }
        StringBuffer head = new StringBuffer("{{" + triCount + "," + quadCount + "," + exCount + "},{");
        for(int i = 0;i < adjacent[vIndex].length;i++) {
            head.append( /*1+*/adjacent[vIndex][i]); // shift in index by 1.
            if(i + 1 < adjacent[vIndex].length)
                head.append(",");
        }
        head.append("}}");
        return head.toString();
    }

    /**
     * Mathematica string format is a format that graphs were stored in by
     * the linear program generator, in the "Kepler98" package.
     * <p>
     * 	// format {0,0,{p1,...,pr}}; pi = {{p,q,r},{adjacent}};
     * p = number of triangles at the vertex,
     * q = number of quads at the vertex,
     * r = number of exceptional regions at the vertex.
     * adjacent_i is a list of vertices, in counterclockwise order around vertex_i
     * These vertices are represented as integers 1,.. in the linear order given by vertexAtFace indices
     * There is an index shift by 1 so that the minimum vertex index is 1.
     * <p>
     * precondition: tempList.length==0 (tempList data is discarded in this format).
     * <p>
     * This format is no longer in use, and it should be deprecated.
     */

    public String toMathematicaString() {
        StringBuffer head = new StringBuffer("{0,0,{\n");
        for(int i = 0;i < faceAtVertex.length;i++) {
            head.append(ptString(i));
            if(i + 1 < faceAtVertex.length)
                head.append(",\n");
        }
        head.append("}}");
        return head.toString();
    }


    /**
     * This method is really for test purposes only.  It prints data about this object.
     */

    public void printGraphDeprecated() {
	// deleted May 2010.  Appears in SVN 1740.
    }
    public static class Test extends util.UnitTest {

        public void testConversion() {
            Formatter f = new Formatter(testString);
            jassert(testString.equals(f.toArchiveString()));
            Graph G = Graph.getInstance(f);
            String S = Formatter.toArchiveString(G);
            jassert(S.equals(testString),"\n"+S+"\n"+testString);
        }
    }
    public static final String testString = "0 23 " + "5 4 5 11 14 10 " + "3 4 10 9 " + "3 9 10 14 " + "3 9 14 13 " + "3 13 14 11 " + "3 13 11 12 " + "3 12 11 6 " + "3 6 11 5 " + "3 6 5 1 " + "3 1 5 0 " + "3 0 5 4 " + "3 0 4 3 " + "3 3 4 9 " + "4 3 9 13 8 " + "3 8 13 12 " + "3 8 12 7 " + "3 7 12 6 " + "3 7 6 1 " + "3 7 1 2 " + "3 2 1 0 " + "3 2 0 3 " + "3 2 3 8 " + "3 8 7 2 ";

    public static void main(String[] args) {
        Formatter form = new Formatter(testString);
        //form.printGraphDeprecated();
    }
}
