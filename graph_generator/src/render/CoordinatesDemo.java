
/**
 * Title:        Graph00<p>
 * Description:  <p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * Company:      University of Michigan<p>
 * @author Thomas C. Hales
 * @version 1.0
 */
package render;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.event.*;
import java.util.*;
import java.graph.*;


/**
 * Constructs a JFrame in the given series and number.
 * A separate thread computes the coordinates.
 * Clicking can update the coordinate positions a bit.
 */
public class CoordinatesDemo extends JApplet {
    private JLabel label;
    final Render render;
    final ArrayList permFaces;

    private void buildUI(Container container, String labelText) {
        container.setLayout(new BoxLayout(container, BoxLayout.Y_AXIS));
        CoordinateArea coordinateArea = new CoordinateArea(this);
        container.add(coordinateArea);
        label = new JLabel(labelText);
        container.add(label);
        coordinateArea.setAlignmentX(LEFT_ALIGNMENT);
        label.setAlignmentX(LEFT_ALIGNMENT); //redundant.
    }

    public static void main(String[] args) {
        Parameter P = Parameter.getExceptionalCase(7);
        String archive = graph.archive.getArchiveString(0, 0);
        Graph G = Graph.getInstance(new Formatter(archive));
        new CoordinatesDemo(G, "HEPT 0 " + Score.squanderLowerBound(G, P));
        String archive2 = graph.archive.getArchiveString( 77);
        G = Graph.getInstance(new Formatter(archive2));
        new CoordinatesDemo(G, "HEPT 77 " + Score.squanderLowerBound(G, P));
    }

    public CoordinatesDemo(Graph G, String labelText, ArrayList permFaces) {
        this.permFaces = permFaces;
        JFrame f = new JFrame("CoordinatesDemo");
        f.addWindowListener(new WindowAdapter()  {

            public void windowClosing(WindowEvent e) {
                render.requestStop();
            //System.exit(0);
            }
        });
        this.buildUI(f.getContentPane(), labelText);
        render = new Render(G);
        f.pack();
        f.setVisible(true);
    }

    public CoordinatesDemo(Graph G, String labelText) {
        this(G, labelText, null);
    }
}
class CoordinateArea extends JPanel {
    final CoordinatesDemo controller;
    Dimension preferredSize = new Dimension(Render.width, Render.height);

    public CoordinateArea(CoordinatesDemo contr) {
        this.controller = contr;
        Border raisedBevel = BorderFactory.createRaisedBevelBorder();
        Border loweredBevel = BorderFactory.createLoweredBevelBorder();
        Border compound = BorderFactory.createCompoundBorder(raisedBevel, loweredBevel);
        setBorder(compound);
        addMouseListener(new MouseAdapter()  {

            public void mousePressed(MouseEvent e) {
                int x = e.getX();
                int y = e.getY();
                controller.render.checkForStop(x, y);
                repaint();
            }
        });
    }

    public Dimension getPreferredSize() {
        return preferredSize;
    }

    public void paintComponent(Graphics g) {
        super.paintComponent(g);
        controller.render.drawAllDot(g);
        controller.render.drawAllEdge(g);
        if(controller.permFaces != null)
            controller.render.drawFace(g, controller.permFaces);
    }
}
class Render implements Runnable {
    final static int width = 400;
    final static int height = 400;
    private double x[]; // x coordinates.
    private double y[]; // y coordinates.
    private Graph G;
    private Coordinate C;
    private Formatter F;
    final static int centerx = width / 2, centery = height / 2, radius = Math.min(width / 2 - 40, height / 2 - 40);

    private static int xcord(double t) {
        return (int)(centerx + radius * t);
    }

    private static int ycord(double t) {
        return (int)(centery + radius * t);
    }

    private static void drawEdge(Graphics g, double x1, double y1, double x2, double y2) {
        g.setColor(Color.black);
        g.drawLine(xcord(x1), ycord(y1), xcord(x2), ycord(y2));
    }

    void drawAllEdge(Graphics g) {
        for(int i = 0;i < x.length ;i++)
            for(int r = 0;r < F.adjacentSize(i);r++) {
                int j = F.adjacent(i, r);
                util.Eiffel.jassert(0<= j && j <x.length);
                drawEdge(g, x[i], y[i], x[j], y[j]);
            }
    }

    void drawAllDot(Graphics g) {
        util.Eiffel.jassert(G.vertexSize()==x.length);
        for(int i = 0;i < G.vertexSize();i++)
            drawDot(g, i, x[i], y[i], true);
    }

    void drawDot(Graphics g, int i, double x1, double y1, boolean drawNumber) {
        g.setColor(Color.blue);
        int x = xcord(x1), y = ycord(y1);
        g.fillOval(x - 5, y - 5, 10, 10);
        if(drawNumber)
            g.drawString(" " + (i /*+1*/), x + 3, y + 3);
    }

    void drawFace(Graphics g, int[] v) {
        g.setColor(Color.yellow);
        Polygon p = new Polygon();
        for(int i = 0;i < v.length;i++) {
            util.Eiffel.jassert(0<= v[i] && v[i] < x.length);
            util.Eiffel.jassert(x.length==y.length);
            p.addPoint(xcord(x[v[i]]), ycord(y[v[i]]));
        }
        g.fillPolygon(p);
    }

    void drawFace(Graphics g, ArrayList L) {
        for(int i = 0;i < L.size();i++)
            drawFace(g, (int[])L.get(i));
    }

    public Render(Graph G) {
        String archive = Formatter.toArchiveString(G);
        F = new Formatter(archive);
        this.G = G;
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
        Thread t = new Thread(this);
        t.start();
    }
    private boolean timeToStop = false;

    public void requestStop() {
        timeToStop = true;
    }

    public void run() {
        for(int i = 0;i < 100000;i++) {
            if(timeToStop)
                break;
            if(C.Move(0.02) < 0.01)
                break;
            for(int j = 0;j < x.length ;j++) {
                x[j] = C.getX(j);
                y[j] = C.getY(j);
            }
        }
    }

    void checkForStop(int x, int y) {
        if(x < 30 && y < 30)
            timeToStop = true;
    }
}
