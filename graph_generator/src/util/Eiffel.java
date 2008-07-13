/**
 * Title:        Testing<p>
 * Copyright:    Copyright (c) Thomas C. Hales<p>
 * @author Thomas C. Hales
 * @version 2001.0
 */
package util;
import java.util.HashMap;

/**
 * Implements Eiffel-style jassertions.  All methods are static.
 */
public class Eiffel {
    private static HashMap H = new HashMap();

    private static java.io.PrintStream out = System.out;

    public Eiffel() {
    }

    public Eiffel(java.io.PrintStream out) {
      this.out=out;
    }

    /**
     * Calls out.println
     */
    public static void message(String S) {
        out.println(S);
    }

    /**
     * Prints the StackTrace with message S and continues execution of the program.
     */
    public static void error(String S) {
        try {
            throw new Exception(S);
        }
        catch(Exception e) {
            out.println(e.getMessage());
            e.printStackTrace(out);
        }
        System.exit(0);
    }

    /**
     * If X is false prints the StackTrace.
     */
    public static void precondition(boolean X) {
        if(!X)
            error("precondition violated");
    }

    /**
     * If X is false prints the StackTrace with message msg, then continues.
     */
    public static void precondition(boolean X, String msg) {
        if(!X)
            error("precondition violated:" + msg);
    }

    /**
     * If X is false, prints the StackTrace and continues.
     */
    public static void jassert(boolean X) {
        if(!X)
            error("jassertion failed");
    }

    public static void jassert(boolean X, String msg) {
      if (!X)
        error("jassertion failed: "+msg);
    }

    /**
     * This is a way to check loop and method invariants.
     * At the beginning the invariant is set, at the end it is verified that
     * the invariant is unchanged.
     * <p>
     * Example:
     *
     * <code><pre>
     * Object key = getKey(new Integer(a));
     * //insert code here...
     *
     * //report error if the value of a has changed:
     * checkKey(key,new Integer(a));
     * </pre>
     * </code>
     * @param value an object that is to stay the same.
     * @returns a key to a hashtable entry holding the value.
     */

    public static Object getKey(Object value) {
        Object key = new Object();
        H.put(key, value);
        return key;
    }

    /**
     * Checks value against hashtable entry.
     * Prints the stack trace if the value is not equal to the one keyed.
     * @param key hashtable key obtained from earlier call to getKey
     * @param object jasserted to equal the key.
     */
    public static void checkKey(Object key, Object value) {
        Object oldValue = H.get(key);
        if(!value.equals(oldValue))
            error("invariant fails");
    }
}
