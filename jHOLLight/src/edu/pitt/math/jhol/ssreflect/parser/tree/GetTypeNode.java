package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * For working with HOL types
 */
public class GetTypeNode extends ObjectNode {
	// Must be a term object
	private ObjectNode tm;
	
	/**
	 * Constructor
	 */
	public GetTypeNode(ObjectNode tm) throws Exception {
		assert(tm != null);
		this.tm = tm;
	}

	@Override
	protected int getType(GoalContext context) {
		return TYPE;
	}

	@Override
	protected boolean isWildCard() {
		return false;
	}

	@Override
	protected String getString() {
		return "@" + tm;
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		if (tm.getType(context) != TERM)
			throw new RuntimeException("GetTypeNode.beginTranslation(): tm should be TERM");

		buffer.append("(type_of ");
		tm.translate(buffer, context);
		buffer.append(")");
	}

}
