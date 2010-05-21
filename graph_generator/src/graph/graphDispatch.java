package graph;

// deprecated!

public class graphDispatch {

    // This class grabs archive strings from graph*.java.
      /**
     * Grabs an archive string from the archive.
     * @param series int 0
     * @param graphNumber range 0..length-1 (java indexing).
     * if series or graphNumber is out of range, null is returned.
     */

    public static String getArchiveString(int graphNumber) {
        String[] data = archive.data;

        if(graphNumber < 0 || graphNumber >= data.length)
            return null;
        return data[graphNumber];
    }

    /**
     * gives the number of graphs in a given series.
     * @param series (ignored)
     */

    public static int size() {
                return archive.data.length;
    }

    public static void main(String[] args) {
    }
}
