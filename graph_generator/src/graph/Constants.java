package graph;
import util.Config;

/**
 * This class contains all the constants that are needed for the graph generator
 * as used in the proof of the Kepler conjecture.  All constants have been
 * converted to exact integer values by multiplying by 1000 and rouding in the
 * correct direction.
 * <p>
 * class Constants : constants but no methods.
 * class Parameter : use constants for things that don't require a graph.
 * class Score     : use constants for things that require a graph.
 */
public class Constants {

    /**
     * This class has no objects. Everything is static.
     */

    private Constants() {
    };

    /**
     * static initialization
     */
    private static Config config;
    private static String propertiesFile = "/Users/thomashales/Desktop/flyspeck_google/source/graph_generator/Kepler2009.properties";
    static {
      try {
        config = new Config(propertiesFile);
        String prop = config.get("testvalue");
        //System.out.println(prop);
      }
      catch (Exception e) {
        System.out.println(propertiesFile + "not found");
      }
    }



    /**
     * true means that we are excluding the configuration of a qrtet and a
     * pentagon that share two edges, with a quadrilateral hull.
     */
    public static boolean getExcludePentQRTet() {
      return excludePentQRTet;
    }
    private final static boolean excludePentQRTet = config.getBooleanProperty("excludePentQRTet",false);


    /**
     * true means that we build the archive from scratch, ignoring what is already there.
     */
    public static boolean ignoreArchive() {
      return ignoreArchive;
    }
    private final static boolean ignoreArchive = config.getBooleanProperty("ignoreArchive",false);


    /**
     * Minimum number of vertices in a graph.
     */
    public static int getVertexCountMin() {
      return vertexCountMin;
    }
    private final static int vertexCountMin = config.getIntProperty("vertexCountMin",1);

    /**
     * Maximum number of vertices in a graph.
     */
    public static int getVertexCountMax() {
      return vertexCountMax;
    }
    private final static int vertexCountMax = config.getIntProperty("vertexCountMax",100);

    /**
     * Maximum number of faces at a vertex containing an exceptional face.
     */
    public static int getFaceCountMaxAtExceptionalVertex() {
      return faceCountMaxAtExceptionalVertex;
    }
    private final static int faceCountMaxAtExceptionalVertex =
      config.getIntProperty("faceCountMaxAtExceptionalVertex",5);

    /**
     * Maximum number of faces at any vertex.
     */
    public static int getFaceCountMax() {
      return faceCountMax;
    }
    private final static int faceCountMax = config.getIntProperty("faceCountMax",6);

    /**
     * Entry[i] contains a lower bound on what is squandered by a polygon with
     * i edges.
     * Values have been multiplied by 1000 and rounded down.
     * Indices out of range correspond to faces that have too many faces to be allowed.
     */
    public static int getFixedSquanderFace(int size) {
      return fixedSquanderFace[size];
    }
    public static int getFixedSquanderFaceLength() {
      return fixedSquanderFace.length;
    }
    private final static int fixedSquanderFace[] =  new int[9];

    static {
      for (int i=0;i<fixedSquanderFace.length;i++) {
        fixedSquanderFace[i]= config.getIntProperty("squanderFace"+i,0);
      }
    }

    /**
     * Entry[i] contains an upper bound on what is scored by a polygon with
     * i edges.
     * Values have been multiplied by 1000 and rounded up.
     * Indices out of range correspond to faces that have too many faces to be allowed.
     */
    public static int getFixedScoreFace(int size) {
      return fixedScoreFace[size];
    }
    private final static int fixedScoreFace[] = new int[9];

    static {
      for (int i=0;i<fixedScoreFace.length;i++) {
        fixedScoreFace[i]= config.getIntProperty("scoreFace"+i,0);
      }
    }

    /**
     * Any graph squandering more than this amount is tossed out.
     */
    public static int getSquanderTarget() {
      return squanderTarget;
    }
    final private static int squanderTarget = config.getIntProperty("squanderTarget",14800);

    /**
     * This is a constant that is used to help initialize the arrays.
     * It can be any value greater than or equal to squanderTarget.
     */
    private final static int x = squanderTarget;

    /**
     * Any graph scoring less than this amount is tossed out.
     */
    public static int getScoreTarget() {
      return scoreTarget;
    }
    final private static int scoreTarget = config.getIntProperty("scoreTarget",8000);

    /** excessTCount[count] is the excess around a vertex at an exceptional cluster
     * having count triangles, and faceCountMaxAtExceptionalVertex-count
     * nontriangles. The length of the array must be fCMAEVertex.
     * <p>
     * For example, assuming faceCountMaxAtExceptionVertex==5,
     * at a vertex with p=3 triangles, a quad, and a pentagon, the faces around that
     * vertex squander at least excessTCount[3]+fixedSquander[4]+fixedSquander[5];
     * <p>
     * Excesses are described at greater length in Kepler98.PartIV.
     */
    public static int getExcessTCount(int size) {
      return excessTCount[size];
    }
    private final static int excessTCount[] =  new int[Constants.faceCountMaxAtExceptionalVertex];

    static {
      for (int i=0;i<excessTCount.length;i++) {
        excessTCount[i]= config.getIntProperty("excessTCount"+i,x);
      }
    }

    /**
     * This table appears in Kepler98.PartIII.Table 5.1.
     * The entry[i][j] is a lower bound on what is squandered by
     * the sum of all the faces around a vertex of type (i,j), where
     * i is the number of triangles and
     * j is the number of quadrilaterals.
     * <p>
     * For example, if there are p=0 triangles and q=3 quadrilaterals,
     * then the 3 quadrilaterals squander at least 7.135 pt, corresponding
     * to the entry 7135 in the table.
     */
    public static int getFixedSquanderVertex(int triCount, int quadCount) {
      return fixedSquanderVertex[triCount][quadCount];
    }
    public static int getFixedSquanderVertexLength() {
      return fixedSquanderVertex.length;
    }
    private final static int fixedSquanderVertex[][] = new int[7][7];
    /* type (i,j).*/   /* PartIII. table 5.1:*/ /* This must be a square array .*/
    static {
      for (int i=0;i<fixedSquanderVertex.length;i++)
      for (int j=0;j<fixedSquanderVertex[i].length;j++) {
        fixedSquanderVertex[i][j]= config.getIntProperty("squanderVertex"+i+""+j,x);
      }
    }


    /**
     * Each row corresponds to a different seed used to initialize graphs.
     * The 3s correspond to triangles, and the 4s correspond to quads.
     * {3,3,4,4,4}, for example, is an arrangement of 5 faces around a vertex,
     * with two consecutive triangles, and three consecutive faces.
     * <p>
     * What is listed here are all the possibilities (up to dihedral symmetry),
     * with p triangles and q quads, such that fixedSquanderVertex[p][q] is
     * not over the target.
     * <p>
     * The order matters, because we may assume in case N that all figures
     * containing seed 0...N-1 have already been generated.
     * <p>
     * These need to be ordered so that cases with the same number of quads and tris
     * appear together.
     */
    public static int[] getQuadCases(int caseNum) {
      return quadCases[caseNum];
    }
    public static int getQuadCasesLength() {
      return quadCases.length;
    }
    private final static int quadCases[][] =  {
         // (p,q)=(2,3)
         {
            3, 3, 4, 4, 4
        }, /*0*/  {
            3, 4, 3, 4, 4
        }, /*1*/  {
            3, 3, 3, 3, 3, 4
        }, /*2   (5,1)*/  {
            4, 4, 4, 4
        }, /*3       (0,4)*/  {
            3, 3, 4
        }, /*4         (2,1)*/  {
            3, 3, 3, 4, 4
        }, /*      (3,2)*/  {
            3, 3, 4, 3, 4
        },  {
            3, 4, 4
        },  {
            3, 4, 4, 4
        }, /*8*/  {
            4, 4, 4
        },  {
            3, 3, 3, 3, 3, 3
        },  {
            3, 3, 4, 4
        }, /*11*/  {
            4, 3, 4, 3
        },  {
            3, 3, 3, 4
        },  {
            3, 3, 3, 3
        },  {
            3, 3, 3, 3, 4
        },  {
            3, 3, 3, 3, 3
        }
    };
    public static class Test extends util.UnitTest {

        public void test_compatibility() {
            int r = fixedSquanderVertex.length;
            //"There are at most 6 faces around each Vertex"
            jassert(r == faceCountMax + 1, "faceCountMax");
            for(int i = 0;i < r;i++)
                jassert(r == fixedSquanderVertex[i].length);
            jassert(vertexCountMin <= vertexCountMax);
            jassert(vertexCountMin >= 0);
            jassert(fixedSquanderFace.length == fixedScoreFace.length);
            jassert(fixedSquanderFace.length <= 9);
            for(int i = 0;i < fixedSquanderFace.length - 1;i++)
                jassert(fixedSquanderFace[i] <= fixedSquanderFace[i + 1], "need monotonicity"+i+" "
                  + fixedSquanderFace[i]+ " "+fixedSquanderFace[i+1]);
            for(int i = 0;i < fixedScoreFace.length - 1;i++)
                jassert(fixedScoreFace[i] >= fixedScoreFace[i + 1], "monotonicity");
            jassert(fixedSquanderFace.length > 5, "need pentagons");
        }
    }

    public static void main(String[] args) {
      System.out.println("vertexCountMin = "+vertexCountMin);
      System.out.println("exclude = "+excludePentQRTet);
    }
}
