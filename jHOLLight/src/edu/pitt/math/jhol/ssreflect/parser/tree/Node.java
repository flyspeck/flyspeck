package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * Abstract base class for tree nodes
 */
public abstract class Node {
	// For generating unique names
	private static int sharedCounter = 0;

	/**
	 * Returns a unique name with the given prefix
	 */
	protected final String getUniqName(String prefix) {
		return prefix + "_" + (sharedCounter++);
	}
	
	/**
	 * Returns a string representation of the node
	 * @return
	 */
	protected abstract String getString();
	
	/**
	 * The main translation method
	 */
	protected abstract void translate(StringBuffer buffer, GoalContext context);
	
	/**
	 * Converts the tree into a HOL Light command
	 * @return
	 */
	public final String toHOLCommand(GoalContext context) {
		// Reset the name generating counter
		sharedCounter = 0;
		
		StringBuffer buffer = new StringBuffer(100);
		translate(buffer, context);
		
		return buffer.toString();
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
