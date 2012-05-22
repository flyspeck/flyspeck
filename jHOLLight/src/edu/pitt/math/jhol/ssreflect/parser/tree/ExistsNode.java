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
	protected void translate(StringBuffer buffer) {
		if (obj.getType() != ObjectNode.TERM && obj.getType() != ObjectNode.UNKNOWN)
			throw new RuntimeException("ExistsNode: the argument must be TERM");

		buffer.append('(');
		obj.translate(buffer);
		buffer.append(" (term_tac exists_tac)");
		buffer.append(')');
	}
}
