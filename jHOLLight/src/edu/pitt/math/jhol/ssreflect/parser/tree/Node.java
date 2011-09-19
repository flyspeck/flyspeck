package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * Abstract base class for tree nodes
 */
public abstract class Node {
	// For generating unique names
	private static int sharedCounter = 0;

	/**
	 * Returns a name for a theorem
	 */
	protected final String getUniqTheoremName() {
		return "th_" + (sharedCounter++);
	}
	
	/**
	 * Returns a string representation of the node
	 * @return
	 */
	protected abstract String getString();
	
	/**
	 * Called before the main translation method
	 */
	protected abstract void beginTranslation(StringBuffer buffer, GoalContext context);
	
	/**
	 * Called after the main translation method
	 */
	protected abstract void endTranslation(StringBuffer buffer);
	
	/**
	 * The main translation method
	 */
	protected abstract void translate(StringBuffer buffer);
	
	/**
	 * Converts the tree into a HOL Light command
	 * @return
	 */
	public final String toHOLCommand(GoalContext context) {
		// Reset the name generating counter
		sharedCounter = 0;
		
		StringBuffer buffer = new StringBuffer(100);
		
		beginTranslation(buffer, context);
		translate(buffer);
		endTranslation(buffer);
		
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
