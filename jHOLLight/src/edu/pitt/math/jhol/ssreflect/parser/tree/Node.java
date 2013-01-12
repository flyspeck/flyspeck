package edu.pitt.math.jhol.ssreflect.parser.tree;

import edu.pitt.math.jhol.caml.CamlBool;
import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;

/**
 * Abstract base class for tree nodes
 */
public abstract class Node {
	// For generating unique names
	private static int sharedCounter = 0;
	
	// An OCaml environment for translating special commands
	private static CamlEnvironment camlEnv = null;

	/**
	 * Returns a unique name with the given prefix
	 */
	protected final String getUniqName(String prefix) {
		return prefix + "_" + (sharedCounter++);
	}

	/**
	 * Returns true if an OCaml environment is defined
	 * @return
	 */
	protected final boolean isEnvDefined() {
		return camlEnv != null;
	}
	
	/**
	 * Tests if the given id defines a theorem
	 * @param id
	 * @return
	 */
	protected final boolean isTheorem(String id) {
		if (camlEnv == null)
			return false;
		
		String cmd = "test_id_thm \"" + id + "\"";
		
		try {
			CamlObject result = camlEnv.execute(cmd, CamlType.BOOL);
			if (result instanceof CamlBool) {
				return ((CamlBool) result).val;
			}
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		
		return false;
	}
	
	/**
	 * Returns a string representation of the node
	 * @return
	 */
	protected abstract String getString();
	
	/**
	 * The main translation method
	 */
	protected abstract void translate(StringBuffer buffer);
	
	/**
	 * Converts the tree into a HOL Light command
	 * @return
	 */
	public final String toHOLCommand() {
		// Reset the name generating counter
		sharedCounter = 0;
		
		StringBuffer buffer = new StringBuffer(10000);
		translate(buffer);
		
		return buffer.toString();
	}
	
	/**
	 * Converts the tree into a HOL Light command using the given OCaml environment
	 * @param env
	 * @return
	 */
	public final String toHOLCommand(CamlEnvironment env) {
		camlEnv = env;
		String result = toHOLCommand();
		camlEnv = null;
		
		return result;
	}

	/**
	 * Returns a command for reversing the effect of the main command
	 */
	public abstract String getRevertCommand();
	
	
	@Override
	public final String toString() {
		return getString();
	}
}
