package graph;
import java.util.ArrayList;

/**
 * This class contains methods that rely on Constants,
 * but not on graphs.  Objects in this class are immutable, depending
 * only on the number n used to instantiate.
 * <p>
 * class Constants : constants but no methods.
 * class Parameter : use constants for things that don't require a graph.
 * class Score     : use constants for things that require a graph.
 */
abstract public class Parameter {

    public static Parameter getQuadCase(int quadCaseNumber) {
        return new QuadParameter(quadCaseNumber);
    }

    public static Parameter getExceptionalCase(int maxGon) {
        return new ExceptionalParameter(maxGon);
    }

    /**
     * Get the maximum number of vertices on a face in the graph.
     */

    abstract int maxGon();

    /**
     * In general, this is just the value of the
     * array Constants.fixedSquanderVertex.
     * In this method it is assumed that previous cases have been handled so
     * that squanderTarget is returned for parameters in the seed of a previous case.
     */

    abstract int squanderVertex(int triangleCount, int quadCount);

    /**
     * A lower bound on what a face squanders.
     * This is only really interesting when there is an exceptional face
     * in the graph.
     * @param ngon number of faces; precondition(ngon>=0)
     */

    abstract int squanderFace(int ngon);

    /**
     * A lower bound on what is squandered by a face with at least
     * ngon vertices.
     * @param ngon lower bound on the number of sides of a face.
     * returns squander lower bound.
     * invariant: squanderFaceStartingAt >= squanderFace.
     * NOTE: In Graph98, this method has a bug, so it always returned squanderTarget.
     */

    abstract int squanderFaceStartingAt(int ngon);

    /** forecast is accurate only at vertices that will eventually be
     * completed without any exceptionals.  It gives the minimum squander
     * given that there are already at least the given number of triangles, quads, and temps
     * (There may be more than this.)
     * @param tri: finished vertex will have at least this many triangles.
     * @param quad: finished vertex will have at least this many quads.
     * @param temps: finished vertex will have at least tri+quad+temp faces.
     * precondition: tri>=0, quad>=0, temp>=0.
     */

    int squanderForecast(int tri, int quad, int temp) {
        if(tri <= 0)
            tri = 0;
        if(quad <= 0)
            quad = 0;
        if(temp <= 0)
            temp = 0;
        if((tri >= forecastD.length) || (quad >= forecastD.length) || (temp >= forecastD.length))
            return Constants.getSquanderTarget();
        return forecastD[tri][quad][temp];
    }
    /**
     * helper array for squanderForecast method.
     */
    private int forecastD[][][];

    /**
     * initialization for squanderForecast method.  called by constructor.
     */

    protected void initForecastD() {
        //1. create array;
        int Q = Constants.getFixedSquanderVertexLength();
        int target = Constants.getSquanderTarget();
        forecastD = new int[Q][Q][Q];
        for(int i = 0;i < Q;i++)
            for(int j = 0;j < Q;j++)
                for(int k = 0;k < Q;k++)
                    forecastD[i][j][k] = target;
        //2. build a list of triples (p,q,squander).
        ArrayList triple = new ArrayList();
        for(int p = 0;p < Q;p++)
            for(int q = 0;q < Q;q++) {
                if(squanderVertex(p, q) < target) {
                    triple.add(new int[] {
                        p, q, squanderVertex(p, q)
                    });
                }
            }
        //3. if (tri+quad+temp<= p+q, tri<=p, quad<= q) then (tri,quad,temp)<-> (p,q).
        for(int k = 0;k < triple.size();k++) {
            int[] T = (int[])triple.get(k);
            int p = T[0];
            int q = T[1];
            int squander = T[2];
            for(int px = 0;px <= p;px++)
                for(int qx = 0;qx <= q;qx++)
                    for(int tx = 0;tx <= p + q - px - qx;tx++) {
                        if(forecastD[px][qx][tx] > squander)
                            forecastD[px][qx][tx] = squander;
                    }
        }
    }

    /**
     * @param tCount number of triangles at the vertex
     * @param qCount number of quads at the vertex
     * @param exCount number of exceptional faces at the vertex.
     * returns excess squander at the vertex.  This value is such that the
     * faces around the given vertex squander at least
     *  pqrExcess+ sum_i fixedSquanderMin[number_of_sides_on_face#i]
     * There must be at least one exceptional at the vertex to get a positive return.
     * postcondition: return>=0.
     * precondition: tCount>=0, qCount>=0, exCount>=0.
     */

    abstract int pqrExcess(int tCount, int qCount, int exCount);
}
class QuadParameter extends Parameter {

    /**
     * This keeps track of the case in the Quad Series.
     * Number of the quadcase, ordered by Constants.quadCases.
     */
    private int quadCaseNumber = -1;

    /**
     * Helper to squanderVertex. Counts triangles in a given seed.
     */

    private static int tCount(int quadCaseNumber) {
        int temp = 0;
        for(int i = 0;i < Constants.getQuadCases(quadCaseNumber).length;i++) {
            if(Constants.getQuadCases(quadCaseNumber)[i] == 3)
                temp++;
        }
        return temp;
    }

    /**
     * Helper to squanderVertex. Counts quads in a given seed.
     */

    private static int qCount(int quadCaseNumber) {
        int temp = 0;
        for(int i = 0;i < Constants.getQuadCases(quadCaseNumber).length;i++) {
            if(Constants.getQuadCases(quadCaseNumber)[i] == 4)
                temp++;
        }
        return temp;
    }

    /**
     * The maximum number of vertices in a polygon.
     */

    int maxGon() {
        return 4;
    }

    /**
     * implements abstract method.
     */

    int squanderVertex(int triangleCount, int quadCount) {
        int target = Constants.getSquanderTarget();
        int len = Constants.getFixedSquanderVertexLength();
        //1. return target if out of range.
        if(triangleCount < 0 || triangleCount >= len)
            return target;
        if(quadCount < 0 || quadCount >= len)
            return target;
        //2. return value if parameters match seed.
        int value = Constants.getFixedSquanderVertex(triangleCount,quadCount);
        if(triangleCount == tCount(quadCaseNumber) && quadCount == qCount(quadCaseNumber))
            return value;
        //3. return target if parameters match an earlier seed.
        for(int i = 0;i < quadCaseNumber;i++) {
            if(triangleCount == tCount(i) && quadCount == qCount(i))
                return target;
        }
        return value;
    }

    /**
     * implements abstract method.
     */

    int squanderFace(int ngon) {
        int target = Constants.getSquanderTarget();
        if(ngon < 0)
            return target;
        if(ngon > 4)
            return target;
        return Constants.getFixedSquanderFace(ngon);
    }

    /**
     * implements abstract method.
     */

    int squanderFaceStartingAt(int ngon) {
        return squanderFace(ngon);
    }

    /**
     * implements abstract method.
     * @precondition: exCount=0.
     */

    int pqrExcess(int tCount, int qCount, int exCount) {
        if(tCount + qCount > Constants.getFaceCountMax())
            return Constants.getSquanderTarget();
        int u = squanderVertex(tCount, qCount) - qCount * squanderFace(4) - tCount * squanderFace(3);
        return Math.max(0, u);
    }

    /**
     * Triangles and Quads only constructor.
     */

    QuadParameter(int quadCaseNumber) {
        this.quadCaseNumber = quadCaseNumber;
        initForecastD();
    }
}
class ExceptionalParameter extends Parameter {

    /**
     * This keeps track of the case in the Exceptional Series.
     */
    private int maxGon = -1;

    /**
     * implements abstract method.
     */

    int maxGon() {
        return maxGon;
    }

    /**
     * Exceptional region graph constructor.
     * The different cases are divided into series according to the maximum number
     * of vertices on a face in the graph.  This is the constructor that is called
     * when there is a face with at least 5 sides.
     * @param ngon Constructs parameters for graphs containing a face with this many
     *  vertices, but no more.
     * precondition: ngon>=5.
     */

    ExceptionalParameter(int maxGon) {
        util.Eiffel.precondition(maxGon >= 5);
        util.Eiffel.precondition(maxGon < Constants.getFixedSquanderFaceLength());
        this.maxGon = maxGon;
        initForecastD();
    }

    /**
     * implements abstract method.
     */

    int squanderVertex(int triangleCount, int quadCount) {
        int target = Constants.getSquanderTarget();
        int len = Constants.getFixedSquanderVertexLength();
        if(triangleCount < 0 || triangleCount >= len)
            return target;
        if(quadCount < 0 || quadCount >= len)
            return target;
        return Constants.getFixedSquanderVertex(triangleCount,quadCount);
    }

    /**
     * implements abstract method.
     */

    int squanderFace(int ngon) {
        int target = Constants.getSquanderTarget();
        if(ngon > maxGon)
            return target;
        int sqMax = Constants.getFixedSquanderFace(maxGon);
        if(ngon == maxGon)
            return sqMax;
        int value = Constants.getFixedSquanderFace(ngon);
        if(ngon < maxGon && (value + sqMax > target))
            return target;
        return value;
    }

    /**
     * implements abstract method.
     */

    int squanderFaceStartingAt(int ngon) {
        int current = Constants.getSquanderTarget();
        for(int i = ngon;i <= maxGon;i++) {
            if(squanderFace(i) < current)
                current = squanderFace(i);
        }
        return current;
    }

    /**
     * implements abstract method.
     */

    int pqrExcess(int tCount, int qCount, int exCount) {
        if(exCount == 0) {
            if(tCount + qCount > Constants.getFaceCountMax())
                return Constants.getSquanderTarget();
            int u = squanderVertex(tCount, qCount) - qCount * squanderFace(4) - tCount * squanderFace(3);
            return Math.max(0, u);
        }
        if(tCount + qCount + exCount != Constants.getFaceCountMaxAtExceptionalVertex())
            return 0;
        return Constants.getExcessTCount(tCount);
    }
}
