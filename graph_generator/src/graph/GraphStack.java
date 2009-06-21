
/**
 * Title:        Graph00<p>
 * Description:  <p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * Company:      University of Michigan<p>
 * @author Thomas C. Hales
 * @version 1.0
 */
package graph;
import java.util.*;
public class GraphStack {

    /**
     * precondition: anything pushed has to have at least one nonFinal face.
     */
    private Stack tentative = new Stack();

    /**
     * contains Invariant objects of all terminal Graphs that are not in archive.
     * precondition: anything pushed has to have all faces isFinal.
     * make it InvariantSetThin for faster pre-run trials.
     */
    private InvariantSet terminal = new InvariantSet();
    private InvariantSet archive = new InvariantSet();
    private Collection hashFound = new HashSet();

    /**
     * build hashtable.
     */

    private void buildExceptionalArchive(stringArchive series,Parameter P) {
	if (!Constants.ignoreArchive()) {
        int sz = series.size();
        for(int i = 0;i < sz;i++) {
            if(0 == (i % 5000))
                System.out.println("***  " + i);
            String S = series.getArchiveString(i);
            Graph G = Graph.getInstance(new Formatter(S));
            util.Eiffel.jassert(Structure.isFinal(G));
	    if (G.vertexSize() < Constants.getVertexCountMin()) continue;
	    if (G.vertexSize() > Constants.getVertexCountMax()) continue;
            if (Score.neglectable(G,P))
                continue;
            Invariant inv = new Invariant(G);
            if(!archive.contains(inv))
                archive.add(inv);
        }
	System.out.println("//archive series/size = "+series.name()+"/"+series.size());
	}
        
    }

    /**
     * Constructor for exceptional series cases.
     */
    GraphStack(stringArchive series, Parameter P) {
        buildExceptionalArchive(series, P);
    }

    /**
     * Similar to buildExceptionalArchive, but it tests that the Graph contains
     * the desired seed before adding it to the archive.
     */
    private void buildQuadArchive(stringArchive series, int casenum, Parameter P) {
	int szx = 0;
	if (!Constants.ignoreArchive()) {
        //0. precondition
        util.Eiffel.jassert(casenum<Constants.getQuadCasesLength());
        int sz = series.size();
	szx = archive.size();
        for(int i = 0;i < sz;i++) {
            String S = series.getArchiveString( i);
            Graph G = Graph.getInstance(new Formatter(S));
            util.Eiffel.jassert(Structure.isFinal(G));
	    if (G.vertexSize() < Constants.getVertexCountMin()) continue;
	    if (G.vertexSize() > Constants.getVertexCountMax()) continue;
            if (!Structure.hasType(G, Constants.getQuadCases(casenum)))
                continue;
            if (Score.neglectable(G,P))
                continue;
            Invariant inv = new Invariant(G);
            if(!archive.contains(inv))
                archive.add(inv);
        }
	}
        System.out.println("//archive series/casenum/size = "+series.name()+"/"+casenum+"/"+szx);
    }

    /**
     * Constructor for quad series cases.
     */
    GraphStack(stringArchive series,int casenum, Parameter P) {
        buildQuadArchive(series, casenum, P);
    }

    /**
     * pushes a graph onto the terminal list, if it hasn't been encountered before.
     */

    private void terminalPush(Graph G) {
        Invariant inv = new Invariant(G);
        if(terminal.contains(inv))
            return ;
        if (G.vertexSize() < Constants.getVertexCountMin()) return;
	if (G.vertexSize() > Constants.getVertexCountMax()) return;
        if(archive.contains(inv)) {
            hashFound.add(new Long(inv.getHash()));
            return ;
        }
        hashFound.add(new Long(inv.getHash()));
        //System.out.println("new graph found!!!! "+inv.getHash());
        //if(bugCounter++ < 0)
        //    new CoordinatesDemo(G, " " + inv.getHash());
        terminal.add(inv);
    }
    private int bugCounter = 0;

    void push(Graph G) {
        boolean isFinal = Structure.isFinal(G);
        if(isFinal)
            terminalPush(G);
        else
            tentative.push(G);
    }

    Graph pop() {
        if(tentative.size() > 0)
            return (Graph)tentative.pop();
        return null;
    }

    int size() {
        return tentative.size();
    }

    Graph[] getTerminalList() {
        Collection C = terminal.values();
        Invariant[] list = (Invariant[])C.toArray(new Invariant[C.size()]);
        Graph[] glist = new Graph[list.length];
        for(int i = 0;i < list.length;i++) {
            glist[i] = list[i].toGraph();
	}
        return glist;
    }

    Long[] getHashFound() {
        return (Long[])hashFound.toArray(new Long[hashFound.size()]);
    }

    int displayOverlookedCases(int maxCount, Parameter p) {
        Long[] Keys = (Long[])archive.keySet().toArray(new Long[0]);
        if (Keys==null) Keys = new Long[0];
        int count = 0;
        for(int i = 0;i < Keys.length;i++) { // break-able
            if(!hashFound.contains(Keys[i])) {
                Invariant[] invList = ((Invariant[])archive.get(Keys[i]).toArray(new Invariant[0]));
                for(int j = 0;j < invList.length;j++) {
                    Graph G = invList[j].toGraph();
                    if(Score.squanderLowerBound(G, p) > Constants.getSquanderTarget())
                        continue;
                    if(Score.scoreUpperBound(G, p) < Constants.getScoreTarget())
                        continue;
                    count++;
                    if (count >= maxCount)
                        break;
                    //new CoordinatesDemo(invList[j].toGraph(), "" + Keys[i]);
                }
            }
        }
        return count;
    }
}
