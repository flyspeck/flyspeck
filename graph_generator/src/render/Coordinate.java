package render;

import java.graph.*;

/**
 * Generate sample coordinates for a graph.
 */
class Coordinate {
    private int hiddenRegion = -1;
    private Formatter gr;
    private double coords[][];
    private static java.util.Random random = new java.util.Random();

    /**
     * Number of entries.
     */
    public int size() {
        return coords.length;
    }

    public Coordinate(Formatter gr) {
        this.gr = gr;
        coords = new double[gr.vertexCount()][2];
    }

    /**
     * Gives the current X-coordinate of the given vertex.
     */

    public double getX(int vertexIndex) {
        util.Eiffel.precondition(0<= vertexIndex && vertexIndex < size());
        return coords[vertexIndex][0];
    }

    /**
     * Gives the current Y-coordinate of the given vertex.
     */

    public double getY(int vertexIndex) {
        util.Eiffel.precondition(0<= vertexIndex && vertexIndex< size());
        return coords[vertexIndex][1];
    }

    /**
     * Set initial values for the coordinates
     * @param initialXY[Formatter f.vertexCount()][2], contains XY coord .
     * @param hidden index of the hiddenRegion.
     * Does nothing if array size is invalid.
     * The array is cloned, so that subsequent changes to initialXY have no effect on
     * coordinates.
     */

    public void setCoordinate(double[][] initialXY, int hidden) {
        util.Eiffel.precondition(initialXY!=null);
        util.Eiffel.precondition(initialXY.length==coords.length);
        for (int i=0;i<initialXY.length;i++) {
            util.Eiffel.precondition(initialXY[i].length==2);
        }
        hiddenRegion = hidden;
        for(int i = 0;i < initialXY.length;i++)
            for(int j = 0;j < 2;j++)
                coords[i][j] = initialXY[i][j];
    }

    /**
     * The hidden region is the face represented at infinity in the graph.
     * @returns index of that face, ordered according to the Formatter object order.
     */

    private int getHiddenRegion() {
        return hiddenRegion;
    }

    /**
     * Sets the hidden region.
     * @param faceNumber is the index of the face to be set as the hiddenRegion
     * Nothing is set if faceNumber is out of range.
     */

    public void setHiddenRegion(int faceNumber) {
        if((faceNumber >= 0) && (faceNumber < gr.faceCount()))
            hiddenRegion = faceNumber;
    }

    /**
     * Sets the hidden region to be the temporary face with the most sides.
     * If there is no temporary face, it calls setHiddenRegion().
     */

    private void setHiddenRegionWithTemp() {
        if(gr.tempCount() == 0) {
            setHiddenRegion();
            return ;
        }
        int i, j, pos = 0, t, temp = -1;
        final int[] tempList = gr.tempList();
        for(j = 0;j < tempList.length ;j++) {
            i = tempList[j];
            t = gr.vertexCount(i);
            if(t > temp) {
                pos = i;
                temp = t;
            }
        }
        hiddenRegion = pos;
    }

    /**
     * Sets the hidden region to be a face with the most sides.
     */

    private void setHiddenRegion() {
        int i, pos = 0, t, temp = -1;
        for(i = 0;i < gr.faceCount();i++) {
            t = gr.vertexCount(i);
            if(t > temp) {
                pos = i;
                temp = t;
            }
        }
        hiddenRegion = pos;
    }

    /**
     * @returns true if the vertex lies in the hidden region.
     * @param vertex int index of a vertex in the Formatter object.
     */

    private boolean IsHidden(int vertex) {
        final int[] vertexList = gr.vertexAtFace(hiddenRegion);
        for(int i = 0;i < vertexList.length;i++) {
            if(vertex == vertexList[i])
                return true;
        }
        return false;
    }


    /**
     * Sets the coordinates on the hiddenRegion in a unit circle, and places
     * all other coordinates in random position.
     * If hiddenRegion has not been initialized, setHiddenRegion is called first.
     */

    public void setRandomCoords() {
        if(gr == null)
            return ;
        if(hiddenRegion < 0)
            setHiddenRegion();
        for(int i = 0;i < coords.length ;i++) {
            coords[i][0] = random.nextDouble() - 0.5;
            coords[i][1] = random.nextDouble() - 0.5;
        }
        int r[] = gr.vertexAtFace(hiddenRegion);
        double N = (double)r.length;
        for(int i = 0;i < r.length;i++) {
            util.Eiffel.jassert(0<= r[i] && r[i] < coords.length);
            coords[r[i]][0] = Math.cos(6.28319 * i / N);
            coords[r[i]][1] = Math.sin(6.28319 * i / N);
        }
    }

    /**
     * Move adjusts the coordinates of the graph, by computing the "badness" function of the
     * graph, computing the gradient, and taking a step in the gradient direction
     * @param stepsize double giving size of gradient movement.  Recommended value: 0.02.
     * @return sum of the abs value of coordinate changes.
     */

    public double Move(double stepsize) {
        int i;
        double backup[][] = new double[coords.length][2];
        for(i = 0;i < coords.length;i++) {
            backup[i][0] = coords[i][0];
            backup[i][1] = coords[i][1];
        }
        double a[][], b[][], c[][];
        a = new double[gr.faceCount()][];
        b = new double[gr.faceCount()][];
        c = new double[gr.faceCount()][];
        util.Eiffel.jassert(a.length == b.length && b.length == c.length);
        for(i = 0;i < a.length ;i++) {
            a[i] = new double[gr.vertexCount(i)];
            b[i] = new double[gr.vertexCount(i)];
            c[i] = new double[gr.vertexCount(i)];
        }
        int k, j0, j1, j2;
        int[] e;
        int count = 0;
        double total = 0.0;
        for(k = 0;k < gr.faceCount();k++) {
            for(i = 0;i < gr.vertexCount(k);i++) {
                e = gr.vertexAtFace(k);
                util.Eiffel.jassert(e.length== gr.vertexCount(k));
                j2 = e[Misc.mod(i + 1, e.length)];
                util.Eiffel.jassert(i<e.length);
                j1 = e[i];
                j0 = e[Misc.mod(i + e.length - 1, e.length)];
                // Use determinant to equalize areas:
                util.Eiffel.jassert(j0<coords.length && j1<coords.length && j2<coords.length);
                util.Eiffel.jassert(j0>=0 && j1>=0 && j2>=0);
                c[k][i] = (coords[j0][0] - coords[j1][0]) * (coords[j2][1] - coords[j1][1]) - (coords[j2][0] - coords[j1][0]) * (coords[j0][1] - coords[j1][1]);
                b[k][i] = coords[j0][1] - coords[j2][1];
                a[k][i] = coords[j2][0] - coords[j0][0];
                count++;
                if(IsHidden(j1)) {
                    count--;
                    c[k][i] = b[k][i] = a[k][i] = 0.0;
                }
                total += c[k][i];
            }
        }
        double average = total / Math.max(1, count);
        double dx[] = new double[gr.vertexCount()], dy[] = new double[gr.vertexCount()];
        util.Eiffel.jassert(dx.length==dy.length);
        for(i = 0;i < dx.length;i++)
            dx[i] = dy[i] = 0.0;
        for(k = 0;k < gr.faceCount();k++) {
            for(i = 0;i < gr.vertexCount(k);i++) {
                j1 = gr.vertexAtFace(k)[i];
                dx[j1] += (c[k][i] - average) * b[k][i];
                dy[j1] += (c[k][i] - average) * a[k][i];
                // July 97 correction:
                if(gr.faceCount(j1) == 2) {
                    for(int h = 0;h < 2;h++) {
                        int hface = gr.faceAtVertex(j1)[h];
                        for(int h2 = 0;h2 < gr.vertexCount(hface);h2++) {
                            int h3 = gr.vertexAtFace(hface)[h2];
                            dx[j1] += (coords[j1][0] - coords[h3][0]);
                            dy[j1] += (coords[j1][1] - coords[h3][1]);
                        }
                    }
                }
            }
        }
        for(i = 0;i < gr.vertexCount();i++) {
            backup[i][0] = coords[i][0] - stepsize * dx[i];
            backup[i][1] = coords[i][1] - stepsize * dy[i];
        }
        // check vertices on the hidden face .
        int r[] = gr.vertexAtFace(hiddenRegion);
        double t1, t2;
        double N = Math.max(1, r.length);
        for(i = 0;i < r.length;i++) {
            t1 = Math.cos(6.28319 * i / N);
            t2 = Math.sin(6.28319 * i / N);
            backup[r[i]][0] = t1;
            backup[r[i]][1] = t2;
        }
        double maxMove = 0;
        for(i = 0;i < backup.length;i++) {
            double uu = Math.abs(backup[i][0] - coords[i][0]) + Math.abs(backup[i][0] - coords[i][0]);
            maxMove += uu;
        }
        for(i = 0;i < backup.length;i++) {
            coords[i][0] = backup[i][0];
            coords[i][1] = backup[i][1];
        }
        return maxMove;
    }


}
