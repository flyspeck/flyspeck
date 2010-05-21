
/**
 * Description: Generate coordinates of a planar graph in DOT format.
 * Company: University of Pittsburgh
 * @author Thomas C. Hales
 */
package render;
import graph.*;

public class Gendot {
    private double x[]; // x coordinates.
    private double y[]; // y coordinates.
    private String dataString;
    private Graph G;
    private Coordinate C;
    private Formatter F;

    private int c(double x) {
	return (new Long(Math.round(400.0*x))).intValue();
    }

    public Gendot(String dataString) {
	this.dataString = dataString;
        F = new Formatter(dataString);
	G = Graph.getInstance(F);
        C = new Coordinate(F);
        C.setRandomCoords();
        for(int i = 0;i < 100;i++)
            C.Move(0.02);
        x = new double[F.vertexCount()];
        y = new double[F.vertexCount()];
        util.Eiffel.jassert(x.length==y.length);
        util.Eiffel.jassert(x.length==F.vertexCount());
        util.Eiffel.jassert(x.length==G.vertexSize());
        for(int i = 0;i < x.length;i++) {
            x[i] = C.getX(i);
            y[i] = C.getY(i);
        }
        for(int i = 0;i < 100000;i++) {
            if(C.Move(0.02) < 0.005) // 0.005 was 0.01
                break;
            for(int j = 0;j < x.length ;j++) {
                x[j] = C.getX(j);
                y[j] = C.getY(j);
            }
        }
	// printout .dot file
	Invariant inv = new Invariant(G);
	System.out.println("//invariant: "+inv.getHash());
	System.out.println("//to generate .gif file");
	System.out.println("//neato -s -n file.dot -Tgif -o file.gif");
	System.out.println("\ngraph G {\n  graph [splines=true,overlap=scale];\n  node [fixedsize=true,shape=circle,height=0.55];\n  graph [bb=\"-440,-440,440,440\"];");
	for (int j=0;j< x.length;j++) {
	    System.out.println("  "+j + " [pos=\"" + c(x[j]) +  "," + c(y[j]) + "\"];");
	}
	System.out.println("node [fixedsize=false,shape=oval,height=0.5];");
	System.out.println(inv.getHash() + " [pos=\"-350,350\"];");
	for(int i = 0;i < x.length ;i++)
            for(int r = 0;r < F.adjacentSize(i);r++) {
                int j = F.adjacent(i, r);
                util.Eiffel.jassert(0<= j && j <x.length);
                if (i < j) { System.out.println("  "+i+ " -- " + j + ";"); }
            }
	System.out.println("}");
    }

    public static void main(String[] args) {

        for (String s: args) {  new Gendot(s); }

	/* sample
      java render/Gendot "65974205892 19 
        4 0 1 2 3 4 0 3 4 5 3 4 3 6 3 6 3 2 3 6 2 7 3 
        7 2 8 3 8 2 1 3 8 1 9 4 9 1 0 5 3 9 5 10 3 10 
        5 4 3 10 4 11 3 11 4 6 3 11 6 7 3 11 7 12 3 
        12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 "
	 */

	/*
	new Gendot("179189825656 21 4 0 1 2 3 3 0 3 4 3 4 3 2 3 4 2 5 3 5 2 6 3 6 2 1 3 6 1 7 3 7 1 8 3 8 1 0 3 8 0 9 3 9 0 4 3 9 4 10 3 10 4 5 3 10 5 11 3 11 5 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ");
	new Gendot("154005963125 20 4 0 1 2 3 4 0 3 4 5 3 4 3 2 3 4 2 6 3 6 2 7 3 7 2 1 3 7 1 8 3 8 1 9 3 9 1 0 3 9 0 5 3 9 5 10 3 10 5 11 3 11 5 4 3 11 4 6 3 11 6 12 3 12 6 7 3 12 7 8 3 12 8 10 3 8 9 10 3 10 11 12 ");
	new Gendot("65974205892 19 4 0 1 2 3 4 0 3 4 5 3 4 3 6 3 6 3 2 3 6 2 7 3 7 2 8 3 8 2 1 3 8 1 9 4 9 1 0 5 3 9 5 10 3 10 5 4 3 10 4 11 3 11 4 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ");
	new Gendot("223336279535 21 4 0 1 2 3 3 0 3 4 3 4 3 5 3 5 3 2 3 5 2 6 3 6 2 1 3 6 1 7 3 7 1 8 3 8 1 0 3 8 0 9 3 9 0 4 3 9 4 10 3 10 4 5 3 10 5 11 3 11 5 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ");
	new Gendot("86506100695 20 4 0 1 2 3 4 0 3 4 5 3 4 3 6 3 6 3 2 3 6 2 7 3 7 2 1 3 7 1 8 3 8 1 9 3 9 1 0 3 9 0 5 3 9 5 10 3 10 5 11 3 11 5 4 3 11 4 6 3 11 6 12 3 12 6 7 3 12 7 8 3 12 8 10 3 8 9 10 3 10 11 12 ");
	new Gendot("161847242261 22 3 0 1 2 3 0 2 3 3 3 2 4 3 4 2 1 3 4 1 5 3 5 1 6 3 6 1 0 3 6 0 7 3 7 0 8 3 8 0 3 3 8 3 9 3 9 3 4 3 9 4 10 3 10 4 5 3 10 5 11 3 11 5 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ");	

	*/
    }

}
