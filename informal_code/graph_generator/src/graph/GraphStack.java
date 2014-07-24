
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
     * This is the stack for partial graphs.
     * precondition: anything pushed has to have at least one nonFinal face.
     */
    private Stack tentative = new Stack();

    /**
     * contains Invariant objects of all terminal Graphs that are not in archive.
     * precondition: anything pushed has to have all faces isFinal.
     * make it InvariantSetThin for faster pre-run trials.
     */
    private InvariantSet terminal = new InvariantSet();

    // full list of P-graphs from stringArchive
    private InvariantSet archivePruned = new InvariantSet(); 

    // full list of hashes of final graphs, whether or not they are already in the archive.
    private Collection hashFound = new HashSet();

    /**
     * build hashtable.
     */

    private void buildGeneralArchive(Parameter P) {
	if (!Constants.ignoreArchive()) {
        int sz = archive.size();
        for(int i = 0;i < sz;i++) {
            String S = archive.getArchiveString(i);
            Graph G = Graph.getInstance(new Formatter(S));
            util.Eiffel.jassert(Structure.isFinal(G));
            if (Score.neglectableFinal(G,P))
                continue;
            Invariant inv = new Invariant(G);
            if(!archivePruned.contains(inv))
                archivePruned.add(inv);
        }
	}
        
    }

    /**
     * Constructor for exceptional archive cases.
     */
    GraphStack(Parameter P) {
        buildGeneralArchive(P);
    }

    /**
     * pushes a graph onto the terminal list, if it hasn't been encountered before.
     * parameter conditions should already be checked before this is called.
     */

    private void terminalPush(Graph G) {
        Invariant inv = new Invariant(G);
        if(terminal.contains(inv))
            return ;
	hashFound.add(new Long(inv.getHash()));
        if(!archivePruned.contains(inv))         terminal.add(inv);
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
        Long[] Keys = (Long[])archivePruned.keySet().toArray(new Long[0]);
        if (Keys==null) Keys = new Long[0];
        int count = 0;
        for(int i = 0;i < Keys.length;i++) { // break-able
            if(!hashFound.contains(Keys[i])) {
                Invariant[] invList = ((Invariant[])archivePruned.get(Keys[i]).toArray(new Invariant[0]));
                for(int j = 0;j < invList.length;j++) {
                    Graph G = invList[j].toGraph();
                    if(Score.squanderLowerBound(G, p) > Constants.getSquanderTarget())
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




    /**
     * deprecated
     * Similar to buildGeneralArchive, but it tests that the Graph contains
     * the desired seed before adding it to the archive.
     */
    private void buildQuadArchiveDeprecated( int casenum, Parameter P) {
	int szx = 0;
	if (!Constants.ignoreArchive()) {
        //0. precondition
        util.Eiffel.jassert(casenum<Constants.getQuadCasesLength());
        int sz = archive.size();
	szx = archive.size();
        for(int i = 0;i < sz;i++) {
            String S = archive.getArchiveString( i);
            Graph G = Graph.getInstance(new Formatter(S));
            util.Eiffel.jassert(Structure.isFinal(G));
            if (!Structure.hasType(G, Constants.getQuadCases(casenum)))
                continue;
            if (Score.neglectableFinal(G,P))
                continue;
            Invariant inv = new Invariant(G);
            if(!archivePruned.contains(inv))
                archivePruned.add(inv);
        }
	}
    }

}
