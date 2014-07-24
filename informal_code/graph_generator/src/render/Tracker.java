
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
import java.graph.*;

/**
 * This displays the progress toward generating a particular graph in the
 * archive.  The graph to be tracked is the template.
 * JFrames showing the progress are displayed, as the cases are encountered.
 * <p>
 * This class is for debugging purposes only.
 * <p>
 * The crucial method is match, which recursively searches for an injective edge-preserving
 * morphism from the partially completed graph to the template.
 */
public class Tracker {

    private int iter = 0; // global variable should be eliminated.
    private Graph template;
    private Face templateFace;

    /**
     * Constructs and generates the baseVertex and templateFace on that vertex.
     */
    public Tracker(Graph template) {
        this.template = template;
        //set baseVertex;
        Vertex bV = (Vertex)template.vertexEnumeration().nextElement();
        long hash = Score.hashVertex(bV);
        for (Enumeration E = template.vertexEnumeration();E.hasMoreElements();/*--*/) {
            Vertex V = (Vertex) E.nextElement();
            long hashV = Score.hashVertex(V);
            if (hashV > hash) {
                hash = hashV;
                bV = V;
            }
        }
        //set templateFace.
        Face F = bV.getAny();
        this.templateFace = F;
        for (int i=0;i<bV.size();i++) {
            if (bV.next(F,i).size()>templateFace.size())
                this.templateFace = bV.next(F,i);
        }
        //check it is the largest.
        for(Enumeration E = template.faceEnumeration();E.hasMoreElements(); /*--*/) {
            F = (Face)E.nextElement();
            util.Eiffel.jassert(F.size() <= templateFace.size());
        }
        template.setBaseVertex(bV);
    }

    /**
     * Try to establish an injection of graphs G to template, sending basepoint to basepoint,
     * and first face to first face (in Enumeration order).
     * If a bijection is found, illustrate it.
     * This method initializes data structures, then calls the recursive match.
     * @param param scoring Parameter, nonessential, but useful for diagnostics.
     */


    public boolean matchAndShow(Graph G, Parameter param) {
        HashMap vertexDict = new HashMap();
        HashMap vInvDict = new HashMap();
        HashMap faceDict = new HashMap();
        Vertex bV = G.getBaseVertex();
        if(bV == null)
            return false;
        vertexDict.put(bV, template.getBaseVertex());
        vInvDict.put(template.getBaseVertex(),bV);
        Face bF = (Face)G.faceEnumeration().nextElement();
        util.Eiffel.jassert(bF.next(bV, 0) == bV);
        util.Eiffel.jassert(bF.isFinal());
        if(bF.size() != templateFace.size())
            return false;
        faceDict.put(bF, templateFace);
        if(match(bV, bF, G, vertexDict, vInvDict, faceDict)) {
            ArrayList permFaces = makePermFaces(G, vertexDict, faceDict);
            new CoordinatesDemo(template, "match and show" + getDiagnosticString(G,param),permFaces);
            //analyzeLastSeen(G, param, vertexDict); //
            iter++;
            return true;
        }
        else
            return false;
    }


    /**
     * helper to matchAndShow to handle the recursion.
     * Adds the vertices of F to the vertexDict<->vInvDict,
     * Adds F to the faceDict
     * then calls itself on each face adjacent to F.
     * @param V starting vertex on Face F, must be in vertexDict
     * @param F starting face for recursion, must be isFinal
     * @param vertexDict maps {Vertices on G -> Vertices on template}
     * @param vInvDict inverse to vertexDict, used to check injectivity
     * @param faceDict maps {final Faces on G -> faces on template}
     */
    private boolean match(Vertex V, Face F, Graph G, HashMap vertexDict, HashMap vInvDict, HashMap faceDict) {
        Face Fx = (Face)faceDict.get(F);
        Vertex Vx = (Vertex)vertexDict.get(V);
        util.Eiffel.jassert(Fx != null && Fx != null);
        for(int i = 0;i < F.size();i++) {
            Vertex W = F.next(V, i);
            Vertex Wx = Fx.next(Vx, i);
            if(!vertexDict.containsKey(W)) {
                if (vInvDict.containsKey(Wx))
                    return false;
                vertexDict.put(W, Wx);
                vInvDict.put(Wx,W);
            }
            else { // vertexDict.containsKey(W);
                if(!vInvDict.containsKey(Wx))
                    return false;
                if(vertexDict.get(W) != Wx)
                    return false;
                if(vInvDict.get(Wx) != W)
                    return false;
            }
        }
        for(int i = 0;i < F.size();i++) {
            Vertex W = F.next(V, i);
            Vertex Wx = Fx.next(Vx, i);
            Face Fnext = W.next(F, 1);
            Face Fxnext = Wx.next(Fx, 1);
            if(!Fnext.isFinal())
                continue;
            if(faceDict.containsKey(Fnext)) {
                if(Fxnext == faceDict.get(Fnext))
                    continue;
                else
                    return false;
            }
            faceDict.put(Fnext, Fxnext);
            if(!match(W, Fnext, G, vertexDict, vInvDict, faceDict))
                return false;
        }
        return true;
    }

    /**
     * integer order is that coming from template.vertexEnumeration.
     * generates Map { Vertices on G -> Integer coordinate number on template }
     * @param vertexDict { Vertices on V -> Vertices on template }
     */
    private HashMap GtoInt(Graph G, HashMap vertexDict) {
        HashMap VtoInt = new HashMap();
         {
            int i = 0;
            for(Enumeration E = template.vertexEnumeration();E.hasMoreElements(); /*--*/) {
                VtoInt.put(E.nextElement(), new Integer(i));
                i++;
            }
        }
        HashMap Gmap = new HashMap();
        for(Enumeration E = G.vertexEnumeration();E.hasMoreElements(); /*--*/) {
            Vertex V = (Vertex)E.nextElement();
            Object Vx = vertexDict.get(V);
            Gmap.put(V, VtoInt.get(Vx));
        }
        return Gmap;
    }

    /**
     * helper to CoordinatesDemo, telling which faces to shade in.
     * Generates an ArrayList of int[]. Each int[] is a list of integer indices
     * in template corresponding to some final face in G.
     * Integer indices are those coming from template.vertexEnumeration.
     * @param vertexDict maps { Vertices on G -> Vertices on template }
     * @param faceDict maps { final Faces on G -> faces on template }
     * The template face is not included, as it is assumed that this one is the
     * one not displayed in CoordinatesDemo.
     */
    private ArrayList makePermFaces(Graph G, HashMap vertexDict, HashMap faceDict) {
        ArrayList L = new ArrayList();
        Vertex[] list = new Vertex[template.vertexSize()];
        HashMap VtoInt = new HashMap();
         {
            int i = 0;
            for(Enumeration E = template.vertexEnumeration();E.hasMoreElements(); /*--*/) {
                list[i] = (Vertex)E.nextElement();
                VtoInt.put(list[i], new Integer(i));
                i++;
            }
        }
        for(Enumeration E = G.faceEnumeration();E.hasMoreElements(); /*--*/) {
            Face F = (Face)E.nextElement();
            if(!F.isFinal())
                continue;
            if(faceDict.get(F) == templateFace)
                continue;
            Vertex V = F.getAny();
            int[] intvalues = new int[F.size()];
            for(int i = 0;i < intvalues.length;i++) {
                Vertex W = F.next(V, i);
                intvalues[i] = ((Integer)VtoInt.get(vertexDict.get(W))).intValue();
            }
            L.add(intvalues);
        }
        return L;
    }

    /**
     * Junk data that is printed when a new CoordinatesDemo JFrame is opened.
     */
    private void analyzeLastSeen(Graph G, Parameter p, HashMap vertexDict) {
        System.out.println("----analyze " + iter);
        if(Structure.nonFinalCount(G) == 0) {
            System.out.println("finished");
        }
        else {
            HashMap Gto = GtoInt(G, vertexDict);
            System.out.println("looking for forced triangles");
            for(Enumeration E = G.vertexEnumeration();E.hasMoreElements(); /*--*/) {
                //1. skip if there is no forced triangle.
                Vertex V = (Vertex)E.nextElement();
                if(V.nonFinalCount() > 0 && Score.ForcedTriangleAt(G, V, p))
                    System.out.println("force vertex at #" + Gto.get(V).toString());
            }
            System.out.println("looking for polygons");
            Face F = Structure.getSmallestTempFace(G);
            System.out.println("temp face has size " + F.size());
            Vertex V = Structure.selectMinimalVertex(F);
            System.out.println("minimal vertex = " + Gto.get(V).toString());
            for(int i = 0;i < F.size();i++)
                System.out.println("...vertex#" + Gto.get(F.next(V, i)).toString());
            if((F.size() == 4) && (Generator.isQuadFriendly(G, p)))
                System.out.println("going to handle quad, face has size 4");
            int polylimit = Score.polyLimit(G, p);
            if((F.size() == 4) && (G.vertexSize() > 5))
                polylimit = Math.min(polylimit, 5);
            System.out.println("polylimit = " + polylimit);
        }
        int sq = Score.squanderLowerBound(G, p);
        System.out.println("squander lower bound =" + sq);
    }

    /**
     * helper to CoordinatesDemo constructor.
     * Junk information to be shown in JLabel of the JFrame.
     */
    private String getDiagnosticString(Graph G,Parameter param) {
            int sq = Score.squanderLowerBound(G, param);
            String sym = (Score.neglectableByBasePointSymmetry(G) ? "symkill" : "symOK");
            String exc = (Constants.getExcludePentQRTet() && Structure.has11Type(G) ? "11kill" : "11OK");
            String has40=(Structure.isFinal(G) && Structure.hasAdjacent40(G) ? "40kill" : "4OK");
            String neg = (Structure.isFinal(G) && Score.neglectable(G, param) ? "neg" : "doneOK");
            if(Structure.isFinal(G)) {
                Invariant inv = new Invariant(G);
                neg = neg + " " + inv.getHash();
            }
            return ""+iter+" "+sq+" "+sym+" "+exc+ " "+has40+" "+neg;
    }

}
