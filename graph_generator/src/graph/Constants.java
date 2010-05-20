package graph;
import util.Config;


/**
 * This class reads all the input parameters that are needed for the graph generator.
 * Unspecified parameters are given default values.
 * Edit the propertiesFile string to use a different properties file.
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
    private static String propertiesFile = "/tmp/graph.properties";
    static {
      try {
        config = new Config(propertiesFile);
        String prop = config.get("testvalue");
        //System.out.println(prop);
	config.getProperties().list(System.out);
      }
      catch (Exception e) {
        System.out.println(propertiesFile + "not found");
      }
    }


    /**
     * true means that we are excluding the configuration any final graph with a deg 2 vertex.
     */
    public static boolean getExcludeDegree2() {
      return excludeDegree2;
    }
    private final static boolean excludeDegree2 = config.getBooleanProperty("excludeDegree2",false);

    /**
     * true means that the program excludes final graphs with  a qrtet and a
     * pentagon that share two edges, with a quadrilateral hull.
     * That is, it excludes final graphs with a vertex of type (1,0,1), where the exceptional
     * face at the vertex is a pentagon.
     */
    public static boolean getExcludePentQRTet() {
      return excludePentQRTet;
    }
    private final static boolean excludePentQRTet = config.getBooleanProperty("excludePentQRTet",false);

    /**
     * true means that we exclude the configuration of two enclosed vertices in a quad cluster.
     */
    public static boolean getExclude2inQuad() {
      return exclude2inQuad;
    }
    private final static boolean exclude2inQuad = config.getBooleanProperty("exclude2inQuad",true); 

/**
     * true means that we exclude the configuration of an enclosed vertices in a triangle cluster.
     */
    public static boolean getExclude1inTri() {
      return exclude1inTri;
    }
    private final static boolean exclude1inTri = config.getBooleanProperty("exclude1inTri",true);


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
     * Maximum cardinality of a face.  If this constant changes, so must the array sizes
     * below.
     */
    private final static int faceCardMax = 8; 

    /**
     * Entry[i] contains a lower bound on what is squandered by a polygon with
     * i edges.
      * Indices out of range correspond to faces that have too many faces to be allowed.
     */
    public static int getFixedSquanderFace(int size) {
      return fixedSquanderFace[size];
    }
    public static int getFixedSquanderFaceLength() {
      return fixedSquanderFace.length;
    }
    private final static int fixedSquanderFace[] =  new int[9]; // must equal 1+faceCardMax.



    /**
     * Entry[i] contains an upper bound on what is scored by a polygon with
     * i edges.
     * Indices out of range correspond to faces that have too many faces to be allowed.
     */
    public static int getFixedScoreFace(int size) {
      return fixedScoreFace[size];
    }
    private final static int fixedScoreFace[] = new int[9];

    static {
      for (int i=0;i<fixedScoreFace.length;i++) {
	  fixedScoreFace[i]= 0; //config.getIntProperty("scoreFace"+i,0);
      }
      util.Eiffel.jassert(fixedScoreFace.length== 1+faceCardMax,
	      "fixedScoreFace initialization error.");
    }

    public static int getMaxFaceSize() {
	int i=fixedSquanderFace.length-1; // was 8.
	 while ((getFixedSquanderFace(i) >= squanderTarget) && (i > 0)) 
	     {  i--; }
	 return i;
    }

    /**
     * Any graph squandering more than this amount is tossed out.
     */
    public static int getSquanderTarget() {
      return squanderTarget;
    }
    final private static int squanderTarget = config.getIntProperty("squanderTarget",1);
    // default was 14800 in svn 1076.  Changed  May 2010.

    /**
     * This is a constant that is used to help initialize the arrays.
     * It can be any value greater than or equal to squanderTarget.
     */
    private final static int x = squanderTarget;

    /**
     * Any graph scoring less than this amount is tossed out.
     * It is time to eliminate this code.  Nothing related to the score is used any more.
     */
    public static int getScoreTarget() {
      return scoreTarget;
    }
    final private static int scoreTarget = -1; // config.getIntProperty("scoreTarget",-1);

    /** excessTCount[count] is the excess around a vertex at an exceptional cluster
     * having count triangles, and faceCountMaxAtExceptionalVertex-count
     * nontriangles. The length of the array must be fCMAEVertex.
     * <p>
     * For example, assuming faceCountMaxAtExceptionVertex==5,
     * at a vertex with p=3 triangles, a quad, and a pentagon, the faces around that
     * vertex squander at least excessTCount[3]+fixedSquander[4]+fixedSquander[5];
     * <p>
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
    static {
      for (int i=0;i<fixedSquanderFace.length;i++) {
	  fixedSquanderFace[i]= (i>faceCardMax? x:config.getIntProperty("squanderFace"+i,x));
      }
    }

    /**
     * Table of "b" values.
     * The entry[i][j] is a lower bound on
     * the sum of the weights of the faces around a vertex of type (i,j,0), where
     * i is the number of triangles and
     * j is the number of quadrilaterals.
     * <p>
     */
    public static int getFixedSquanderVertex(int triCount, int quadCount) {
      return fixedSquanderVertex[triCount][quadCount];
    }
    public static int getFixedSquanderVertexLength() {
      return fixedSquanderVertex.length;
    }
    private final static int fixedSquanderVertex[][] = new int[10][10]; // was 7.
    /* type (i,j).*/   
    static {
	util.Eiffel.jassert(fixedSquanderVertex.length == fixedSquanderVertex[0].length,
                "square b matrix required");
	util.Eiffel.jassert(fixedSquanderVertex.length > max(faceCountMax),
		"b matrix out of bounds");
      for (int i=0;i<fixedSquanderVertex.length;i++)
      for (int j=0;j<fixedSquanderVertex[i].length;j++) {
	  fixedSquanderVertex[i][j]= x;
      }
      for (int i=0;i<=faceCountMax;i++)
      for (int j=0;j<=faceCountMax;j++) {
        fixedSquanderVertex[i][j]= config.getIntProperty("squanderVertex"+i+""+j,x);
      }
    }


    /**
     *  This section is deprecated.
     *  It was generated using the properties of graphs for the 1998 proof of Kepler.
     *  It is not sufficiently general for our purposes now.

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

    private final static int quadCases[][] = {};

    //    private final static int quadCases[][] =  {
    //	{3,3,3,3,3,3,3}, /* added 2009 */
    //	{ 4, 4 }, /* added 2009 */
    // { 3, 3, 4, 4, 4 }, /*0*/  // (p,q)=(2,3)
    //         { 3, 4, 3, 4, 4 }, /*1*/  
    //         { 3, 3, 3, 3, 3, 4}, /*2   (5,1)*/ 
    //         { 4, 4, 4, 4 }, /*3       (0,4)*/  
    //	 { 3, 3, 4 }, /*4         (2,1)*/  
    //	 { 3, 3, 3, 4, 4  }, /*      (3,2)*/  
    //         { 3, 3, 4, 3, 4 }, 
    //	 { 3, 4, 4  }, /* (1,2) */
    //         { 3, 4, 4, 4 }, /*8     (1,3) */ 
    //         { 4, 4, 4 },  
    //	 { 3, 3, 3, 3, 3, 3},  
    //	 { 3, 3, 4, 4 }, /*11*/ 
    //	 { 4, 3, 4, 3},  
    //	 { 3, 3, 3, 4 },  
    //	 { 3, 3, 3, 3}, 
    //	 { 3, 3, 3, 3, 4 },  
    //    { 3, 3, 3, 3, 3 }
    //    };

  static  {
           int r = fixedSquanderVertex.length;
            //"There are at most r faces around each Vertex"
            util.Eiffel.jassert(r == faceCountMax + 1, "faceCountMax");
		util.Eiffel.jassert(fixedSquanderFace.length== 1+faceCardMax,
                    "faceSquanderFace initialization error.");
            for(int i = 0;i < r;i++)
                util.Eiffel.jassert(r == fixedSquanderVertex[i].length);
            util.Eiffel.jassert(vertexCountMin <= vertexCountMax);
            util.Eiffel.jassert(vertexCountMin >= 0);
            util.Eiffel.jassert(fixedSquanderFace.length <= 9);
            for(int i = 0;i < fixedSquanderFace.length - 1;i++)
                util.Eiffel.jassert(fixedSquanderFace[i] <= fixedSquanderFace[i + 1], "need monotonicity"+i+" "
                  + fixedSquanderFace[i]+ " "+fixedSquanderFace[i+1]);
            util.Eiffel.jassert(fixedSquanderFace.length > 5, "need pentagons");
	    //Score is deprecated:
            //util.Eiffel.jassert(fixedSquanderFace.length == fixedScoreFace.length);
            //for(int i = 0;i < fixedScoreFace.length - 1;i++)
            //    util.Eiffel.jassert(fixedScoreFace[i] >= fixedScoreFace[i + 1], "monotonicity");
}

    public static class Test extends util.UnitTest {

        public void test_compatibility() {
 
        }
    }

    public static void main(String[] args) {
    }
}
