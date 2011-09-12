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
	protected int getType() {
		return TYPE;
	}

	@Override
	protected boolean isWildCard() {
		return false;
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		tm.beginTranslation(buffer, context);
		
		if (tm.getType() != TERM)
			throw new RuntimeException("GetTypeNode.beginTranslation(): tm should be TERM");
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		tm.endTranslation(buffer);
	}

	@Override
	protected String getString() {
		return "@" + tm;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append("(type_of ");
		tm.translate(buffer);
		buffer.append(")");
	}

}
