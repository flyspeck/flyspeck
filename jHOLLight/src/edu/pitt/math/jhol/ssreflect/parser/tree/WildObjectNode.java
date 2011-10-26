package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * _
 */
public class WildObjectNode extends ObjectNode {
	/**
	 * Default constructor
	 */
	public WildObjectNode() {
	}
	
	@Override
	protected String getString() {
		return "_";
	}

	@Override
	protected int getType(GoalContext context) {
		return UNKNOWN;
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		throw new RuntimeException("wildcard.translate(): unimplemented");
		
	}

	@Override
	protected boolean isWildCard() {
		return true;
	}

}
