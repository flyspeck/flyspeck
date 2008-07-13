
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
public class GraphTest {

    /**
     * More tests for Graph class.
     * create the Graph of Formatter.testString in two ways and compare.
     * See FormatterStringConstruct.gif.  This is impossible to follow without
     * looking at the gif.
     */
    public static class Test extends util.UnitTest {

        public void TestSeed() {
            for (int seedNumber=0;seedNumber<Constants.getQuadCasesLength();seedNumber++) {
                Graph Seed = Graph.getInstance(Constants.getQuadCases(seedNumber));
                Vertex Vfinal=null;
                //CoordinatesDemo C = new CoordinatesDemo(Seed,"seed ="+seedNumber);
                for (Enumeration E=Seed.vertexEnumeration();E.hasMoreElements();/*--*/) {
                    Vertex V = (Vertex) E.nextElement();
                    if (V.nonFinalCount()==0) {
                        Vfinal=V;
                    }
                    else {
                        jassert(V.nonFinalCount()==1,"nonFinal is "+V.nonFinalCount()+" "+V);
                        jassert(V.faceCount(3,4)+1==V.size(),"face count is "+V.faceCount(3,3)+" "+V.faceCount(4,4)+" test"+seedNumber);
                        jassert(V.size()<4,"V.size="+V.size()+" "+seedNumber);
                    }
                }
                jassert(Vfinal!=null);
                jassert(Structure.hasType(Seed,Constants.getQuadCases(seedNumber)));
            }
        }

        public static Face getAddOn(Graph G) {
            for(Enumeration E = G.faceEnumeration();E.hasMoreElements(); /*--*/) {
                Face F = (Face)E.nextElement();
                if(F.size() > 3 && !F.isFinal())
                    return F;
            }
            return null;
        }

        private static int position(Face F, Graph G) { // number 1...
            int count = 1;
            for(Enumeration E = G.faceEnumeration();E.hasMoreElements(); /*--*/) {
                if(F.equals(E.nextElement()))
                    return count;
                ++count;
            }
            return -1;
        }

        public static Face getFace(int count, Graph G) { // number 1...
            Enumeration E = G.faceEnumeration();
            for(int i = 1;i < count;i++)
                E.nextElement();
            return (Face)E.nextElement();
        }

        private static void print(Graph G) {
            String S = Formatter.toArchiveString(G);
            Formatter f = new Formatter(S);
            f.printGraph();
        }

        public void testGraphConstructor() {
            //1. Face F1
            Graph G = Graph.getInstance(5);
            jassert(getFace(1, G).size() == 5);
            for(int i = 0;i < 5;i++) {
                Face FF = getFace(1, G);
                Vertex VV = FF.getAny();
                jassert(FF.next(VV, i).getHeight() == 0);
            }
            //F2.
            Face F = getAddOn(G);
            jassert(position(F, G) == 2);
            Vertex V = G.getBaseVertex();
            jassert(F.size() == 5);
            Vertex[] V0 = new Vertex[] {
                F.next(V, -1), V, null
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(V0[2].getHeight() == 1);
            jassert(getFace(1, G).size() == 5);
            jassert(getFace(2, G).size() == 3);
            //F3.
            F = getAddOn(G);
            V = V0[1];
            jassert(G.getBaseVertex() == V);
            jassert(F.size() == 6);
            V0 = new Vertex[] {
                F.next(V, -1), V, null
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(V0[2].getHeight() == 1);
            //F4.
            F = getAddOn(G);
            V = V0[1];
            jassert(G.getBaseVertex() == V);
            jassert(F.size() == 7);
            V0 = new Vertex[] {
                F.next(V, -1), V, null
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(getFace(4, G).next(V0[2], 0) == V0[2]);
            jassert(V0[2].getHeight() == 1);
            //F5.
            F = getAddOn(G);
            V = V0[1];
            jassert(G.getBaseVertex() == V);
            jassert(F.size() == 8);
            V0 = new Vertex[] {
                F.next(V, -1), V, F.next(V, 1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            //F6.
            F = getAddOn(G);
            V = V0[2];
            jassert(G.getBaseVertex() == V0[1]);
            jassert(F.size() == 7);
            jassert(Structure.highGon(G.getBaseVertex()) == 5);
            jassert(position(F, G) == 6);
            Face F2 = getFace(1, G);
            V0 = new Vertex[] {
                V, F2.next(V, -1), F.next(V, -1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            //F7.
            F = getAddOn(G);
            V = V0[2];
            V0 = new Vertex[] {
                V, F.next(V, 1), null
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(V0[2].getHeight() == 1);
            //F8.
            F = getAddOn(G);
            V = V0[0];
            V0 = new Vertex[] {
                V, F.next(V, 1), null, getFace(4, G).next(V, 1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(V0[2].getHeight() == 2);
            //F9.
            F = getAddOn(G);
            V = V0[3];
            jassert(F.size() == 7);
            jassert(G.vertexSize() == 10);
            jassert(G.faceSize() == 9);
            jassert(getFace(8, G).size() == 4);
            V0 = new Vertex[] {
                V, F.next(V, 1), null
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(V0[2].getHeight() == 2);
            //F10.
            F = getAddOn(G);
            V = V0[0];
            V0 = new Vertex[] {
                V, F.next(V, 1), getFace(3, G).next(V, 1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            //F11.
            F = getAddOn(G);
            V = V0[2];
            V0 = new Vertex[] {
                V, F.next(V, 1), null
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(V0[0].getHeight() == 1);
            jassert(V0[2].getHeight() == 2);
            //F12.
            F = getAddOn(G);
            V = V0[1];
            V0 = new Vertex[] {
                V, null, F.next(V, -1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(V0[1].getHeight() == 3);
            //F13.
            F = getAddOn(G);
            V = V0[0];
            V0 = new Vertex[] {
                V, F.next(V, 1), F.next(V, -1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            //F14.
            F = getAddOn(G);
            jassert(F.size() == 8);
            jassert(G.faceSize() == 14);
            jassert(G.vertexSize() == 13);
            V = V0[1];
            V0 = new Vertex[] {
                V, null, F.next(V, -1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(V0[0].getHeight() == 2);
            jassert(V0[1].getHeight() == 3);
            //F15.
            F = getAddOn(G);
            V = V0[0];
            V0 = new Vertex[] {
                V, F.next(V, 1), F.next(V, -1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            //F16.
            F = getAddOn(G);
            V = V0[1];
            jassert(getFace(1, G).next(G.getBaseVertex(), 2) == F.next(V, 2));
            V0 = new Vertex[] {
                V, F.next(V, 2), F.next(V, -1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(Structure.nonFinalCount(G) == 2);
            F = Structure.getSmallestTempFace(G);
            jassert(F.size() == 3);
            //F17.
            F = getAddOn(G);
            jassert(F.size() == 6);
            jassert(G.faceSize() == 18);
            V = V0[2];
            V0 = new Vertex[] {
                V, F.next(V, 1), null
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(V0[2].getHeight() == 1);
            //F18.
            F = getAddOn(G);
            jassert(F.size() == 7);
            V = V0[0];
            V0 = new Vertex[] {
                V, F.next(V, 1), F.next(V, -1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            //F19.
            F = getAddOn(G);
            V = V0[2];
            V0 = new Vertex[] {
                V, F.next(V, 1), F.next(V, -1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            //F20.
            F = getAddOn(G);
            V = V0[1];
            V0 = new Vertex[] {
                V, F.next(V, 2), F.next(V, -1)
            };
            G = G.add(new Face[] {
                F
            }, V0);
            jassert(!Structure.isFinal(G));
            jassert(Structure.nonFinalCount(G) == 3);
            Structure.makeTrianglesFinal(G);
            jassert(Structure.isFinal(G));
            //done!
            jassert(getAddOn(G) == null);
            Invariant X = new Invariant(G);
            Invariant Y = new Invariant(Graph.getInstance(new Formatter(Formatter.testString)));
            jassert(X.Isomorphic(Y));
            //test Structure class a bit more.
            F = getFace(11, G);
            V = Structure.selectMinimalVertex(F);
            jassert(getFace(2, G).next(V, 0) == V);
            jassert(Structure.highGon(V) == 3);
            jassert(!Structure.has11Type(G));
        }
    }
}
