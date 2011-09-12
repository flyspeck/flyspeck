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
	protected int getType() {
		return UNKNOWN;
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
	}

	@Override
	protected void translate(StringBuffer buffer) {
		// TODO Auto-generated method stub
		throw new RuntimeException("wildcard.translate(): unimplemented");
		
	}

	@Override
	protected boolean isWildCard() {
		return true;
	}

}
