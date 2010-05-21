package graph;
import java.util.*;
import java.lang.*;
import java.math.BigInteger;


/**
 * Constructs numerical hashes for a graph G in such a way that it is relatively
 * easy to detect graph isomorphisms.  The main method is Isomorphic, which determines
 * whether two graphs (wrapped as Invariant objects) are isomorphic.  This method
 * either produces a graph bijection or does an exhaustive search proving that
 * no such bijection can exist.
 * <p>
 * The name of the class comes from the fact that the hashes are constructed as
 * invariants of the isomorphism class of the graph.
 * <p>
 * The isomorphisms can be orientation reversing, and the private variables keep
 * track of the mirror image of graph, to aid in determining orientation-reversing
 * isomorphisms.
 */
public class Invariant {
    final private Graph G;
    private Invariant mirror;
    final private Hashtable vertexInvariant = new Hashtable(); // { Vertex-> hashcode }
    final private Hashtable faceInvariant = new Hashtable(); // { Face -> hashcode }
    //final private long hash;
    final private BigInteger hashB;
    //private static final long prime = 15485863; //Prime[10^6];
    private static final long prime = 252097800623L; //Prime[10^10];
    private static final BigInteger primeB = new BigInteger("252097800623",10);
    final private Dart[] coupleList; //return value of selectDart

    public Invariant(Graph G) {
        this(G, new Invariant(G.copy(true, new Vertex[0], new Face[0]), null));
        mirror.mirror = this;
    }

    private Invariant(Graph G, Invariant M) {
        this.G = G;
        mirror = M;
        hashB = computeInvariant(G, vertexInvariant, faceInvariant); //side-effects to args.
        coupleList = selectDart(G, vertexInvariant, faceInvariant);
    }

    // BigInteger ops:
    private static long longOf(BigInteger j) {
	return j.longValue();
    }
    private static BigInteger sum(BigInteger i,BigInteger j) {
	return (i.add(j)).mod(primeB);
    }
    private static BigInteger mul(BigInteger i,BigInteger j) {
	return (i.multiply(j)).mod(primeB);
    }
    private static BigInteger sq(BigInteger a) {
	return mul(a,a);
    }


    /**
     * This is a long with the property that nonisomorphic graphs are unlikely
     * to get the same return value.  Mirror images have the same hash.
     */

    public long getHash() {
        return longOf(sum(sq(hashB),sq(mirror.hashB)));
    }
 
    /**
     * A value depending only on the cyclic ordering.
     * $\sum x_i^2 x_{i+1} mod p$.
     */

    private static BigInteger symcyc(BigInteger x[]) {
        BigInteger total = BigInteger.ZERO;
        for(int i = 0;i < x.length;i++) {
            total = sum(total,mul(x[(i + 1) % x.length],sq(x[i])));
        }
        return total;
    }

    //Table[Random[Integer,{1,10^6}]//Prime,{i,0,10}]
    private static BigInteger[] vHash = {
        new BigInteger("7184057"), new BigInteger("6907723"), new BigInteger("12428951"), new BigInteger("846749"), new BigInteger("9432197"), new BigInteger("2488777"),
        new BigInteger("6632911"), new BigInteger("5368189"), new BigInteger("13123039"), new BigInteger("3197849"), new BigInteger("4405699")

    };



    /**
     * Returns a hash of the proper iso class of the vertex.
     */

    private static BigInteger vertexInvariant0(Vertex V) {
        BigInteger[] x = new BigInteger[V.size()];
        Face F = V.getAny();
        for(int i = 0;i < V.size();i++)
            x[i] = vHash[V.next(F, i).size() % vHash.length];
        return symcyc(x);
    }

    /**
     * Returns a hash of the proper iso class of a vertex.
     * invariant: faceHash is read-only.
     */

    private static BigInteger vertexInvariant(Vertex V, Hashtable faceHash) {
        BigInteger[] x = new BigInteger[V.size()];
        Face F = V.getAny();
        for(int i = 0;i < V.size();i++)
            x[i] = ((BigInteger)faceHash.get(V.next(F, i)));
        return symcyc(x);
    }

    /**
     * Returns a hash of the proper iso class of a face.
     * invariant: vertexHash is read-only.
     */

    private static BigInteger faceInvariant(Face F, Hashtable vertexHash) {
        BigInteger[] x = new BigInteger[F.size()];
        Vertex V = F.getAny();
        for(int i = 0;i < F.size();i++)
            x[i] = ((BigInteger)vertexHash.get(F.next(V, i)));
        return symcyc(x);
    }

    /**
     * computes an invariant for a graph G; storing values of vertex and face invariants in
     * the hashtables.
     * precondition: vertexHash!=null; faceHash!=null;
     * both vertexHash and faceHash are cleared before they are used.
     * @param vertexHash: Hashtable { Vertex -> hash code}.  Side-effect generates this hashtable.
     * @param faceHash: Hashtable { Face -> hash code}. Side-effect generates this hashtable.
     */

    static private BigInteger computeInvariant(Graph G, Hashtable vertexHash, Hashtable faceHash) {
        BigInteger accumulator = BigInteger.ZERO;
        Vertex[] vertexList = new Vertex[G.vertexSize()];
        Face[] faceList = new Face[G.faceSize()];

         /* 1. initialize vertexList and vertexHash */{
            vertexHash.clear();
            int i = 0;
            Enumeration vEnumeration = G.vertexEnumeration();
            while(vEnumeration.hasMoreElements()) {
                Vertex V = (Vertex)vEnumeration.nextElement();
                vertexList[i++] = V;
                vertexHash.put(V, vertexInvariant0(V));
            }
        }

         /* 2. initialize faceList and faceHash */{
            faceHash.clear();
            int i = 0;
            BigInteger L0 = BigInteger.ZERO;
            Enumeration fEnumeration = G.faceEnumeration();
            while(fEnumeration.hasMoreElements()) {
                Face F = (Face)fEnumeration.nextElement();
                faceList[i++] = F;
                faceHash.put(F, L0);
            }
        }

        /* 3. iterate a couple of times */
        final int iterLimit = 3; // was 2.
        for(int level = 0;level < iterLimit;level++) {
            for(int i = 0;i < faceList.length;i++) {
                Face F = faceList[i];
                BigInteger hashB = faceInvariant(F, vertexHash);
                faceHash.put(F, hashB);
                accumulator = sum(accumulator,sq(hashB));
            }
            for(int i = 0;i < vertexList.length;i++) {
                Vertex V = vertexList[i];
                BigInteger hashB = vertexInvariant(V, faceHash);
                vertexHash.put(V, hashB);
                accumulator = sum(accumulator,sq(hashB));
            }
        }
        return accumulator;
    }

    /**
     * helper for selectDart
     */

    private static BigInteger hash(Dart C, Hashtable Vertexhash, Hashtable Facehash) {
	BigInteger primeC = new BigInteger("39731340001");
        BigInteger hashV = (BigInteger)Vertexhash.get(C.getV());
        BigInteger hashF = (BigInteger)Facehash.get(C.getF());
        return sum(sq(hashV),mul(primeC,sq(hashF)));
    }

    /**
     * This canonically picks out a (smallest possible) set of Dart objects
     * with the same hash code.
     * @param Vertexhash: Hashtable { Vertex -> hash }
     * @param Facehash: Hashtable { Face -> hash }
     * invariant: G, Vertexhash, and Facehash are read-only.
     */

    private static Dart[] selectDart(Graph G, Hashtable Vertexhash, Hashtable Facehash) {
        //1. get a complete list of couples.
        Dart[] fullC;
          /* block 1. */{
            Enumeration E = G.vertexEnumeration();
            if(G.vertexSize() == 0)
                return new Dart[0];
            Vertex V = (Vertex)G.vertexEnumeration().nextElement();
            Face F = V.getAny();
            Dart C = new Dart(V, F);
            fullC = Dart.getDarts(C, G);
        }
        //2. for each hash count the number of times it occurs.
        Hashtable InvariantCounter = new Hashtable(); // { hash -> count}
        for(int i = 0;i < fullC.length;i++) {
            Dart C = fullC[i];
            BigInteger hashC = hash(C, Vertexhash, Facehash);
            Integer count = (Integer)InvariantCounter.get(hashC);
            if(count == null)
                count = new Integer(0);
            InvariantCounter.put(hashC, increment(count, 1));
        }
        //3. pick out the smallest hash among those that appear least often.
        BigInteger smallestHash = primeB.add(primeB); // > Max Hash.
        int leastCount = Integer.MAX_VALUE;
        for(Enumeration E = InvariantCounter.keys();E.hasMoreElements(); /*--*/) {
            BigInteger hashC = (BigInteger)E.nextElement();
            int count = ((Integer)InvariantCounter.get(hashC)).intValue();
            if(count < leastCount) {
                leastCount = count;
                smallestHash = hashC;
            }
            if(count == leastCount) {
                if(hashC.compareTo(smallestHash) < 0)
                    smallestHash = hashC;
            }
        }
        //4. pick all Darts with that invariant.
        Collection bestC = new ArrayList();
        for(int i = 0;i < fullC.length;i++) {
            if((hash(fullC[i], Vertexhash, Facehash)).compareTo(smallestHash)==0)
                bestC.add(fullC[i]);
        }
        //5. return.
        return (Dart[])bestC.toArray(new Dart[bestC.size()]);
    }


    /**
     * helper function for selectDart.
     */

    private static Integer increment(Integer a, int i) {
        return new Integer(i + a.intValue());
    }

    /**
     * Returns true if the underlying graphs are isomorphic, and false otherwise.
     * Guaranteed to determine if they are isomorphic or not.
     *
     * @param A the Invariant being compared to this.  It is left unmodified.
     *
     * A.Isomorphic(B) returns the same value as B.Isomorphic(A).
     */

    public boolean Isomorphic(Invariant inv) {
        return (ProperlyIsomorphic(inv) || mirror.ProperlyIsomorphic(inv));
    }


    /**
     * Returns true if there is an orientation preserving isomorphism between the
     * graphs.  Guaranteed to return true if they are properly isomorphic.
     * Guaranteed to return false if not.
     * @param inv Invariant being compared to this.
     * invariant: no side-effects.
     */

    public boolean ProperlyIsomorphic(Invariant inv) {
        if(this.hashB.compareTo(inv.hashB)!=0)
            return false;
        if(this.coupleList.length != inv.coupleList.length)
            return false;
        //1. if they are isomorphic, they have the same couple list up to relabelling, so [0] matches.
        for(int i = 0;i < coupleList.length;i++) {
            if(ProperIsoWithBaseDart(inv, coupleList[i], inv.coupleList[0]))
                return true;
        }
        return false;
    }

    /**
     * helper for ProperlyIsomorphic
     */

    private boolean ProperIsoWithBaseDart(Invariant inv, Dart thisC, Dart invC) {
        Dart[] thisList = thisC.getDarts(thisC, this.G);
        Dart[] invList = invC.getDarts(invC, inv.G);
        if(thisList.length != invList.length)
            return false;
        //1. build hashtable mapping vertices and faces.
        Hashtable vertexMap = new Hashtable();
        Hashtable faceMap = new Hashtable();
        for(int i = 0;i < thisList.length;i++) {
            vertexMap.put(thisList[i].getV(), invList[i].getV());
            faceMap.put(thisList[i].getF(), invList[i].getF());
        }
        //2. check neighborhoods on vertices.
        for(Enumeration E = vertexMap.keys();E.hasMoreElements(); /*--*/) {
            Vertex V = (Vertex)E.nextElement();
            Vertex V2 = (Vertex)vertexMap.get(V);
            Face F = V.getAny();
            Face F2 = (Face)faceMap.get(F);
            for(int i = 0;i < V.size();i++) {
                if(!(V2.next(F2, i) == faceMap.get(V.next(F, i))))
                    return false;
            }
        }
        //3. check neighborhoods on faces.
        for(Enumeration E = faceMap.keys();E.hasMoreElements(); /*--*/) {
            Face F = (Face)E.nextElement();
            Face F2 = (Face)faceMap.get(F);
            Vertex V = (Vertex)F.getAny();
            Vertex V2 = (Vertex)vertexMap.get(V);
            for(int i = 0;i < F.size();i++) {
                if(!(F2.next(V2, i) == vertexMap.get(F.next(V, i))))
                    return false;
            }
        }
        return true;
    }

    public Graph toGraph() {
        return G;
    }

 public static void printCollisions() { 
            // slow test.. make it public to run.
            Hashtable H = new Hashtable(); // { hash -> graph }
            for(int i = 0;i < archive.size();i++) {
                String S = archive.getArchiveString(i);
                Graph G = Graph.getInstance(new Formatter(S));
                Invariant inv = new Invariant(G);
                Long hash = new Long(inv.getHash());
                if(H.containsKey(hash)) {
                    Invariant inv2 = (Invariant)H.get(hash);
                    if(!inv.Isomorphic(inv2))
                        System.out.println("//nonisomorphic graphs with same hash found... " + i + " " + hash);
                    else
                        System.out.println("//duplicate found... " + i + " "+ hash);
                }
                H.put(hash, inv);
            }
        }

    public static class Test extends util.UnitTest {

        public void test_invariant() {
            for(int i = 2;i < 3;i++) {
                //(PENT,2) happens to be assymetric, these tests rely on this fact.
                String S = archive.getArchiveString( i);
                Graph G = Graph.getInstance(new Formatter(S));
                Formatter f = new Formatter(S);
                Invariant X = new Invariant(G);
                jassert(X.ProperlyIsomorphic(X), "self id failed at " + i);
                Graph G2 = G.copy(true, new Vertex[0], new Face[0]);
                Invariant X2 = new Invariant(G2);
                jassert((X.hashB).compareTo(X2.hashB) != 0);
                jassert(X.getHash() == X2.getHash());
                jassert(!X.ProperlyIsomorphic(X2));
                jassert(X.Isomorphic(X2));
                Graph G3 = G.copy(false, new Vertex[0], new Face[0]);
                Invariant X3 = new Invariant(G3);
                jassert(X3.hashB.compareTo(X.hashB) ==0);
                jassert(X3.hashB.compareTo(X2.mirror.hashB) ==0);
                jassert(X.ProperlyIsomorphic(X3));
            }
        }

       
    }

    public static void main(String[] args) {

       for (String s: args) {  
         Formatter f = new Formatter(s);
	Graph G = Graph.getInstance(f);
	Invariant inv = new Invariant(G);
	Long hash = new Long(inv.getHash());
	System.out.println("hash : "+hash);
       }
    }


}
