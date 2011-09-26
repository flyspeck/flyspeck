package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * Object node: a term or a theorem
 */
public abstract class ObjectNode extends Node {
	// Type constants
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
	protected abstract int getType();
	
	/**
	 * Sets the interpretation of a wild card
	 */
	protected void setWildCardInterpretation(String interpretation) {
		throw new RuntimeException("Not a wild card");
	}
}
