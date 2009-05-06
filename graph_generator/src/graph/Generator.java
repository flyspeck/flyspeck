package graph;
import java.util.*;

/**
 * Generate all graphs with a given set of properties.
 */
public class Generator {
    private static GraphStack stack;
    private Parameter param;
    private static String path = "C:\\Documents and Settings\\Thomas Hales\\Desktop\\";
    /**
     * Push onto the stack all possible ngons constructed in face F
     * using the edge terminating at vertex V.
     */

    private void generatePolygon(int ngon, Vertex V, Face F, Graph G) {
        //1. initialize
        int outer = F.size();
        boolean neglectable[][] = new boolean[outer][outer];
        initNeglectTable(neglectable, V, F, G);
        /* genpoly loop */
        EnumerationLoop:for(Enumeration E = new Enumerator(ngon, outer);E.hasMoreElements(); /*--*/) {
            int[] list = (int[])E.nextElement();
            //1. continue if it has an edge (i,i+1) that is neglectable.
            for(int i = 0;i + 1 < list.length;i++) {
                if((list[i + 1] > list[i]) && ((i == 0) || (list[i] > list[i - 1]))) {
                    if(neglectable[list[i]][list[i + 1]])
                        continue EnumerationLoop;
                }
            }
            //2. convert list to an array of vertices.
            Vertex[] poly = new Vertex[list.length];
            for(int i = 0;i < list.length;i++) {
                if(i == 0 || list[i] != list[i - 1])
                    poly[i] = F.next(V, list[i]);
                else
                    poly[i] = null;
            }
            //3. push onto stack.
            if(!Score.neglectable(poly, F, G, param))
                Xpush(G.add(new Face[] {
                    F
                }, poly));
        }
    }
    /**
     * helper for generatePolygon
     * Score.neglectableEdge is called many times with the same parameters, and
     * this makes a cache of the values.
     * @param neglectable write-only
     * @param V vertex on face F on Graph G.
     */

    private void initNeglectTable(boolean[][] neglectable, Vertex V, Face F, Graph G) {
        util.Eiffel.precondition(neglectable.length == F.size());
        for(int i = 0;i < F.size();i++)
            for(int j = i + 1;j < F.size();j++) {
                if(Score.neglectableEdge(F.next(V, i), F.next(V, j), F))
                    neglectable[i][j] = true;
                else
                    neglectable[i][j] = false;
            }
        for(int i = 0;i < F.size();i++)
            for(int j = i + 1;j < F.size();j++)
                neglectable[j][i] = neglectable[i][j];
        for(int i = 0;i < F.size();i++)
            neglectable[i][i] = false;
    }
    /**
     * helper for LOOP
     * Helps LOOP decide whether to handle it through handleQuad,
     *  or through the generic polygon procedure.
     * A quadFriendly graph is one where the following conditions hold.
     *      (1) no further exceptionals can be added.
     *      (2) no new vertex of type (2,1) can be added.
     *      (3) no new vertex of type (0,2) can be added.
     * These two types are vertices enclosed in a quad cluster.
     */

    public static boolean isQuadFriendly(Graph G, Parameter param) {
        if (G.vertexSize()<6)
            return false;
        int s = Score.faceSquanderLowerBound(G, param) + Score.ExcessNotAt(null, G, param);
        if (s + param.squanderFaceStartingAt(5) < Constants.getSquanderTarget())
            return false;
        if (s + param.squanderVertex(2, 1) < Constants.getSquanderTarget())
            return false;
        if (s + param.squanderVertex(0, 2) < Constants.getSquanderTarget())
            return false;
        return true;
    }
    /**
     * helper for handleQuad
     * Makes a clone with Face F final.
     * @param F a Face on G
     */

    private Graph makeQuadFinal(Face F, Graph G) {
        //0. preconditions
        util.Eiffel.precondition(F.size() == 4);
        Object key = util.Eiffel.getKey(new Integer(Structure.nonFinalCount(G)));
        //1. exit if neglectable.
        boolean doquad = true;
        Vertex V = F.getAny();
        for(int i = 0;i < 4;i++)
            if(Score.neglectableModification(G, 0, 1, 0, -1, F.next(V, i), param))
                return null;
        //2. make clone and push it
        Face[] faceList = new Face[] {
            F
        };
        G = G.copy(false, new Vertex[0], faceList);
        util.Eiffel.jassert(faceList != null);
        util.Eiffel.jassert(faceList[0] != null);
        faceList[0].setFinal(true);
        util.Eiffel.checkKey(key, new Integer(Structure.nonFinalCount(G) + 1));
        return G;
    }
    /**
     * helper for handleQuad
     * splits a quad case into two triangles from V to F.next(V,2).
     * @param V Vertex on F, a Face on Graph G.
     */

    private Graph splitQuad(Vertex V, Face F, Graph G) {
        Vertex Vlist[] = new Vertex[4];
        for(int i = 0;i < 4;i++)
            Vlist[i] = F.next(V, i);
        if(Score.neglectableEdge(V, F.next(V, 2), F)) {
            util.Eiffel.jassert(false);
            return null;
            }
        for(int i = 0;i < 4;i++) {
            if(Score.neglectableModification(G, 1 + Misc.mod(i + 1, 2), 0, 0, -1, Vlist[i], param))
                return null;
        }
        return G.add(new Face[] {F}, new Vertex[] {V, F.next(V, 1), F.next(V, 2)});
    }
    /**
     * helper for handleQuad
     * Do40 takes a nonFinal face with 4 vertices and pushes a new graph with 4
     * triangles around a vertex of type (4,0).
     * @param F a nonFinal face with 4 vertices.
     */

    private Graph Do40(Face F, Graph G) {
        util.Eiffel.precondition(!F.isFinal());
          /*1. get out if it squanders over target. */{
            int faceSqu = Score.faceSquanderLowerBound(G, param);
            int exN = Score.ExcessNotAt(null, G, param);
            int forecast = param.squanderForecast(4, 0, 0);
            if(faceSqu + exN + forecast >= Constants.getSquanderTarget())
                return null;
        }
        //2. get out if it is neglectable;
        Vertex V = F.getAny();
        for(int i = 0;i < 4;i++) {
            if(Score.neglectableModification(G, 2, 0, 0, -1, F.next(V, i), param))
                return null;
        }
        //3. add first triangle
        Vertex[] newV = new Vertex[] {
            null, V, F.next(V, 1)
        };
        Face[] fList = new Face[] {
            F
        };
        G = G.add(fList, newV); //sets fList and newV.
        util.Eiffel.jassert(fList[0].size() == 3);
        //4. add second triangle.
        F = fList[0]; //first triangle.
        V = newV[0]; //new vertex.
        util.Eiffel.jassert(V.size() == 2);
        F = V.next(F, 1); // pentagon;
        util.Eiffel.jassert(F.size() == 5);
        util.Eiffel.jassert(!F.isFinal());
        fList[0] = F;
        newV = new Vertex[] {
            V, F.next(V, 1), F.next(V, 2)
        };
        G = G.add(fList, newV);
        util.Eiffel.jassert(fList[0].size() == 3);
        //5. add third triangle.
        V = newV[0];
        F = fList[0];
        F = V.next(F, -1);
        fList[0] = F;
        util.Eiffel.jassert(F.size() == 4);
        util.Eiffel.jassert(!F.isFinal());
        newV = new Vertex[] {
            V, F.next(V, 1), F.next(V, 2)
        };
        G = G.add(fList, newV);
        //4. fourth triangle remains, will be made final later.
        return G;
    }
    /**
     * helper for LOOP
     * Calls various helpers to create all quad combinations.
     */

    private void handleQuad(Face F, Graph G) {
        util.Eiffel.precondition(F.size() == 4);
        Graph G_temp;
        if(null != (G_temp = makeQuadFinal(F, G)))
            Xpush(G_temp);
        if(null != (G_temp = Do40(F, G)))
            Xpush(G_temp);
        Vertex V = F.getAny();
        if(null != (G_temp = splitQuad(V, F, G)))
            Xpush(G_temp);
        V = F.next(V, 1);
        if(null != (G_temp = splitQuad(V, F, G)))
            Xpush(G_temp);
    }
    /**
     * helper for LOOP to look for and treat forced triangles.
     * @return true if a forced triangle was found
     * side-effect a new graph with the forced triangle is pushed onto the stack.
     */

    private boolean handleForcedTriangle(Graph G) {
        for(Enumeration E = G.vertexEnumeration();E.hasMoreElements(); /*--*/) {
            //1. skip if there is no forced triangle.
            Vertex V = (Vertex)E.nextElement();
            if(V.nonFinalCount() == 0)
                continue;
            if(!Score.ForcedTriangleAt(G, V, param))
                continue;
            //2. find a temp face.
            Face F = V.getAny();
            while(F.isFinal())
                F = V.next(F, 1);
            util.Eiffel.jassert(!F.isFinal());
            Vertex A = F.next(V, 1);
            Vertex B = F.next(V, -1);
            //3. handle divide.
            if(Score.neglectableModification(G, 1, 0, 0, -1, A, param))
                return true;
            if(Score.neglectableModification(G, 1, 0, 0, -1, B, param))
                return true;
            if(Score.neglectableEdge(A, B, F))
                return true;
            G = G.add(new Face[] {
                F
            }, new Vertex[] {
                V, A, B
            });
            Xpush(G);
            return true;
        }
        return false; // No forced triangles were found.
    }
    /**
     * This pushes only if standard tests are satisfied.
     */

    private void Xpush(Graph G) {
        Structure.makeTrianglesFinal(G);
        //if(track
        //    track.matchAndShow(G, param);
	
        if (!Score.neglectable(G, param))
            stack.push(G);
	
    }




    /**
     * This is the main loop used in generating the series of graphs.
     * returns false when the stack of unprocessed partial graphs goes to zero.
     * returns true while there is more to be done.
     */

    void loop(Graph G) {
	//0. vertex max
	//if(G.vertexSize()> Constants.getVertexCountMax()) return;
        //1. triangles first
        if(handleForcedTriangle(G))
            return ;
        //2. pick smallest face.
        Face F = Structure.getSmallestTempFace(G);
        //3. pick best vertex.
        Vertex V = Structure.selectMinimalVertex(F);
        //4. handle quads.
        if((F.size() == 4) && (isQuadFriendly(G, param))) {
            handleQuad(F, G);
            return ;
        }
        //5. handle general face.
        int polylimit = Score.polyLimit(G, param);
        if((F.size() == 4) && (G.vertexSize() > 5))
            polylimit = Math.min(polylimit, 5);
        for(int i = 3;i <= polylimit;i++)
            generatePolygon(i, V, F, G);
    }
    /**
     * This generates all the graphs in the exceptional series.
     * @param NGON each graph must have a face with NGON vertices, and no faces
     * with more.
     */

    public static void generateExceptionalSeries(int NGON) {
        Parameter param = Parameter.getExceptionalCase(NGON);
        int series;
        switch(NGON) {
            case 5:
                series = graphDispatch.ALL;
                break;

            case 6:
                series = graphDispatch.ALL;
                break;

            case 7:
                series = graphDispatch.ALL;
                break;

            default:
                series = graphDispatch.ALL;
                break;
        }
        Graph Seed = Graph.getInstance(NGON);
        //if (true)
          //series = graphDispatch.ALL;
        String outfile = path + "newExcept"+NGON+".java";
        //String archive = graphDispatch.getArchiveString(graphDispatch.ALL, 2393);

        Generator gen = new Generator(param, Seed, series, new GraphStack(series, param), outfile);
    }
    /**
     * This takes the Quad case number and generates a list of all the graphs
     * satisfying the list of properties growing out of the Constants file.
     */

    public static void generateQuadSeries(int casenum) {
        //1. print banner.
        int[] type = Constants.getQuadCases(casenum);
        String S = "***** ";
        for (int i=0;i<type.length;i++)
            S = S + " "+type[i];
        System.out.println("//********  "+casenum+"/"+Constants.getQuadCasesLength()+":  "+S);
        //2. initialize.
        int series = graphDispatch.ALL;
        //if (true)
        //  series = graphDispatch.ALL;
        Parameter param = Parameter.getQuadCase(casenum);
        GraphStack stack = new GraphStack(series, casenum, param);
        Graph Seed = Graph.getInstance(Constants.getQuadCases(casenum));
        String outfile = path + "newQuad"+casenum+".java";
        Generator gen = new Generator(param, Seed, series, stack, outfile);
    }

    /**
     * Constructor, generates all possible Graphs.
     * @param param Scoring parameters
     * @param Seed Graph
     * @param series int constant from GraphDispatch.# describing the series.
     */

    Generator(Parameter param, Graph Seed, int series, GraphStack stack, String outfile) {
        //1. initialize
        //this.track = track;
        this.param = param;
        this.stack = stack;
        int counter = 0;
        util.CalendarExtension initCal = new util.CalendarExtension();
        stack.push(Seed);
        //2. main loop
        while(stack.size() > 0) {
            loop(stack.pop());
            if(0 == Misc.mod(++counter, 50000)) /* adapt as needed */ {
                System.out.print("// stack sizes = " + stack.size());
                System.out.print("// cases found= " +stack.getHashFound().length);
                System.out.println("// cases considered= " + counter);
            }
        }
        //3. print some diagnostics
        util.CalendarExtension finCal = new util.CalendarExtension();
        System.out.println("// elapsed time: "+((double)(finCal.toLong()-initCal.toLong()))/1000.+" secs ");
        System.out.println("// case completed: stack size = " + stack.size());
        System.out.println("// final loop count = " + counter);
        Graph[] list = stack.getTerminalList();
        //for(int i = 0;i < Math.min(list.length, 0);i++)
        //    new CoordinatesDemo(list[i], "" + i);
        System.out.println("// terminalList = " + list.length);
        System.out.println("// total acceptable found = " + stack.getHashFound().length);
        int over = stack.displayOverlookedCases(5, param);
        System.out.println("// some missed cases = "+over);
        //4. Write out the new cases:
        if (list.length>0) try {
            System.out.println("//********************");
            java.io.FileWriter F = new java.io.FileWriter(outfile,false/*dont append*/);

            for (int i=0;i<list.length;i++) {
                F.write("\""+Formatter.toArchiveString(list[i])+"\",\n");
            }
            F.close();
        }
        catch (Exception e) {
            System.out.println("//save failed");
        }
    }

    public static void main(String[] args) {

        /**
        
        **/

        for (int i=5;i<9;i++) {
	    System.out.println("//***** generating exceptional series "+i);
            Generator.generateExceptionalSeries(i);
            Graph[] glist = stack.getTerminalList();
	    for (int j=0;j<glist.length;j++) {
		System.out.println("\""+Formatter.toArchiveString(glist[j])+"\",");
	    }
	}
	for (int i=0;i<Constants.getQuadCasesLength();i++) {
            Generator.generateQuadSeries(i);
	    Graph[] glist = stack.getTerminalList();
	    for (int j=0;j<glist.length;j++) {
		System.out.println("\""+Formatter.toArchiveString(glist[j])+"\",");
	    }
        }
        //System.out.println(archive.graphPE);

        /**
        String[] hex = new String[] {
        "0 14 6 0 1 2 3 4 5 3 0 5 4 3 0 4 6 3 6 4 7 3 7 4 3 3 7 3 8 3 8 3 2 3 8 2 9 3 9 2 1 3 9 1 0 4 9 0 6 10 3 10 6 7 3 8 9 10 3 10 7 8 ",
        "0 16 6 0 1 2 3 4 5 3 0 5 4 3 0 4 6 3 6 4 7 3 7 4 3 3 7 3 8 3 8 3 2 3 8 2 9 3 9 2 1 3 9 1 10 3 10 1 0 4 10 0 6 11 3 11 6 7 3 11 7 8 3 9 10 11 3 11 8 9 ",
        "0 16 6 0 1 2 3 4 5 3 0 5 4 3 0 4 6 3 6 4 3 3 6 3 7 3 7 3 8 3 8 3 2 3 8 2 1 3 8 1 9 3 9 1 10 3 10 1 0 4 10 0 6 11 3 11 6 7 3 11 7 9 3 7 8 9 3 9 10 11 ",
        };
        for (int i=0;i<hex.length;i++) {
          new CoordinatesDemo(Graph.getInstance(new Formatter(hex[i])),"hex "+i);
        }
        **/
    }
}

