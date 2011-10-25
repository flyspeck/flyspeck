package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * exists x
 */
public class ExistsNode extends TacticNode {
	// Object
	private final ObjectNode obj;
	
	/**
	 * Default constructor
	 */
	public ExistsNode(ObjectNode obj) {
		assert(obj != null);
		this.obj = obj;
	}

	@Override
	protected String getString() {
		return "exists " + obj;
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		obj.beginTranslation(buffer, context);
		if (obj.getType() != ObjectNode.TERM && obj.getType() != ObjectNode.UNKNOWN)
			throw new RuntimeException("ExistsNode: the argument must be TERM (or UNKNOWN)");
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		obj.endTranslation(buffer);
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		buffer.append("exists_tac ");
		obj.translate(buffer);
		buffer.append(')');
	}
}
