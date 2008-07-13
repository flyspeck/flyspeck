
/**
 * Title:        Graph00<p>
 * Description:  <p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * Company:      University of Michigan<p>
 * @author Thomas C. Hales
 * @version 1.0
 */
package render;

import java.util.*;
import graph.*;


public class Test1 {

    public Test1() {

    }

    public static void show(int series, int number) {

    }

    public static void proc() {
        Parameter P = Parameter.getQuadCase(4);
        int count = 0;
        int top = graph.graphDispatch.size(graph.graphDispatch.ALL);
        for(int i = 0;i < top;i++) {
            String archive = graph.graphDispatch.getArchiveString(graph.graphDispatch.ALL, i);
            Graph G = Graph.getInstance(new Formatter(archive));
            int sq = Score.squanderLowerBound(G, P);
            int sc = Score.scoreUpperBound(G, P);
            if(sq < Constants.getSquanderTarget() && sc >= Constants.getScoreTarget()) {
                count++;
                if(count < 5)
                    new CoordinatesDemo(G, "QUAD " + i + " " + sq + " " + sc);
            }
            Invariant inv = new Invariant(G);
            if
                (  inv.getHash() == 13116654
                || inv.getHash() == 7097145
                )
                {
                System.out.println(""+inv.getHash()+" = QUAD#" + i);
                new CoordinatesDemo(G,"QUAD "+ i+ " "+sq+" "+sc +" "+inv.getHash());
            }
        }
        System.out.println(count);
    }

    public static void main(String[] args) {
    /**
      int[] v = {27,39,27,39,29,40,41};
      for (int i=0;i<4;i++) {
        int num = v[i];
        String archive = graph.graphDispatch.getArchiveString(graph.graphDispatch.ALL,num);
        Graph G = Graph.getInstance(new Formatter(archive));
        new CoordinatesDemo(G,"new dodec "+num);
      }
    **/

    //proc();
    }
}
