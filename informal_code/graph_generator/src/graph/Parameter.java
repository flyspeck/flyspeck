package graph;
import java.util.ArrayList;
import java.math.BigInteger;	

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


    public static Parameter getGeneralCase(int maxGon) {
        return new GeneralParameter(maxGon);
    }

    /**
     * Get the maximum cardinality of a face in the graph.
     */

    abstract int maxGon();

    /**
     * In general, this is just the value of the
     * array Constants.fixedTableWeightB.
     * In this method it is assumed that previous cases have been handled so
     * that squanderTarget is returned for parameters in the seed of a previous case.
     */

    abstract int tableWeightB(int triangleCount, int quadCount);

    /**
       returns true if it is a previously considered case.
     */
    /*
    abstract boolean priorCase(int[] type);
    */

    /**
     * A lower bound on what a face squanders.
     * This is only really interesting when there is an exceptional face
     * in the graph.
     * @param ngon number of faces; precondition(ngon>=0)
     */

    abstract int tableWeightD(int ngon);

    /**
     * A lower bound on what is squandered by a face with at least
     * ngon vertices.
     * @param ngon lower bound on the number of sides of a face.
     * returns squander lower bound.
     * invariant: tableWeightDStartingAt >= tableWeightD.
     * NOTE: In Graph98, this method has a bug, so it always returned squanderTarget.
     */

    abstract int tableWeightDStartingAt(int ngon);

    /** forecast is accurate only at vertices that will eventually be
     * completed without any exceptionals.  It gives the minimum squander
     * given that there are already at least the given number of triangles, quads, and temps
     * (There may be more than this.)
     * @param tri: finished vertex will have at least this many triangles.
     * @param quad: finished vertex will have at least this many quads.
     * @param temps: finished vertex will have at least tri+quad+temp faces.
     * precondition: tri>=0, quad>=0, temp>=0.
     */

    int squanderForecastPureB(int tri, int quad, int temp) {
        if(tri <= 0)
            tri = 0;
        if(quad <= 0)
            quad = 0;
        if(temp <= 0)
            temp = 0;
        if((tri >= forecastB.length) || (quad >= forecastB.length) || (temp >= forecastB.length))
            return Constants.getSquanderTarget();
        return forecastB[tri][quad][temp];
    }
    /**
     * helper array for squanderForecastPureB method.
     */
    private int forecastB[][][];

    /**
     * initialization for squanderForecastPureB method.  called by constructor.
     */

    protected void initForecastB() {
        //1. create array;
        int Q = Constants.getFixedTableWeightBLength();
        int target = Constants.getSquanderTarget();
        forecastB = new int[Q][Q][Q];
        for(int i = 0;i < Q;i++)
            for(int j = 0;j < Q;j++)
                for(int k = 0;k < Q;k++)
                    forecastB[i][j][k] = target;
        //2. build a list of triples (p,q,squander).
        ArrayList triple = new ArrayList();
        for(int p = 0;p < Q;p++)
            for(int q = 0;q < Q;q++) {
                if(tableWeightB(p, q) < target) {
                    triple.add(new int[] {
                        p, q, tableWeightB(p, q)
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
                        if(forecastB[px][qx][tx] > squander)
                            forecastB[px][qx][tx] = squander;
                    }
        }
    }

    /**
     * @param tCount number of triangles at the vertex
     * @param qCount number of quads at the vertex
     * @param exCount number of exceptional faces at the vertex.
     * The parameters tCount,qCount,exCount are counts for a final vertex.
     * Let A be the set of tCount + qCount triangle and quad vertices at the vertex.
     * return value is such that
     * sum_{F\in A} \tau(F) >= pqrExcess + tCount d(3) + qCount d(4).
     * postcondition: return>=0.
     * precondition: tCount>=0, qCount>=0, exCount>=0.
     */

    abstract int pqrExcess(int tCount, int qCount, int exCount);
}
class GeneralParameter extends Parameter {

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
     * General region graph constructor.
     * @param ngon Constructs parameters for graphs containing a face with this many
     *  vertices, but no more.
     * precondition: ngon>=3. 
     */

    GeneralParameter(int maxGon) {
	//	boolean QL = Constants.getExclude2inQuad();
        util.Eiffel.precondition(maxGon >= 3);
        util.Eiffel.precondition(maxGon < Constants.getFixedTableWeightDLength());
        this.maxGon = maxGon;
        initForecastB();
    }

    /**
     * implements abstract method.
     */

    int tableWeightB(int triangleCount, int quadCount) {
        int target = Constants.getSquanderTarget();
        int len = Constants.getFixedTableWeightBLength();
        if(triangleCount < 0 || triangleCount >= len)
            return target;
        if(quadCount < 0 || quadCount >= len)
            return target;
        return Constants.getFixedTableWeightB(triangleCount,quadCount);
    }

    /**
     * implements abstract method.
     */

    int tableWeightD(int ngon) {
        int target = Constants.getSquanderTarget();
        if(ngon > maxGon)
            return target;
        int sqMax = Constants.getFixedTableWeightD(maxGon);
        if(ngon == maxGon)
            return sqMax;
        int value = Constants.getFixedTableWeightD(ngon);
        if(ngon < maxGon && (value + sqMax > target))
            return target;
        return value;
    }

    /**
     * implements abstract method.
     */

    int tableWeightDStartingAt(int ngon) {
        int current = Constants.getSquanderTarget();
        for(int i = ngon;i <= maxGon;i++) {
            if(tableWeightD(i) < current)
                current = tableWeightD(i);
        }
        return current;
    }

    /**
     * implements abstract method.
     */

    int pqrExcess(int tCount, int qCount, int exCount) {
	util.Eiffel.jassert(Constants.getSquanderTarget()>=0,"param:pqrExcess post");
        if(exCount == 0) {
            if(tCount + qCount > Constants.getNodeCardMax())
                return Constants.getSquanderTarget();
            int u = tableWeightB(tCount, qCount) 
		- qCount * tableWeightD(4) - tCount * tableWeightD(3);
            return Math.max(0, u);
        }
        if(tCount + qCount + exCount != Constants.getNodeCardMaxAtExceptionalVertex())
            return 0;
	int u = Constants.getTableWeightA(tCount);
	util.Eiffel.jassert(u>=0,"param:pqrExcess post");
	    return u;
    }
}





