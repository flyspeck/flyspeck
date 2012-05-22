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
	protected String getString() {
		return "@" + tm;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		if (tm.getType() != TERM && tm.getType() != UNKNOWN)
			throw new RuntimeException("GetTypeNode.beginTranslation(): tm should be TERM");

		buffer.append("(fun arg_tac -> ");
		tm.translate(buffer);
		buffer.append("(fun arg -> arg_tac (Arg_type (type_of (get_arg_term arg))))");
		buffer.append(')');
	}

}
