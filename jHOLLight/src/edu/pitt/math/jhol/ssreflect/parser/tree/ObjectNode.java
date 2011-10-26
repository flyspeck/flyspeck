package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * Object node: a term, a theorem, or a type.
 * Terms and types are translated as is.
 * Theorems are translated into a tactic which takes one theorem-tactic as the argument.
 */
public abstract class ObjectNode extends Node {
	// Type constants
	// UNKNOWN = THEOREM when the object is translated
	protected static final int UNKNOWN = 0;
	protected static final int TERM = 1;
	protected static final int THEOREM = 2;
	protected static final int TYPE = 3;
	
	@Override
	public String getRevertCommand() {
		throw new RuntimeException("ObjectsNode: cannot be reverted");
	}
	
	/**
	 * Returns true if the object itself or the first object in an application
	 * is a wild card
	 */
	protected abstract boolean isWildCard(); 
	
	/**
	 * Returns object's type
	 */
	protected abstract int getType(GoalContext context);
	
	/**
	 * Sets the interpretation of a wild card
	 */
	protected void setWildCardInterpretation(String interpretation) {
		throw new RuntimeException("Not a wild card");
	}
}
