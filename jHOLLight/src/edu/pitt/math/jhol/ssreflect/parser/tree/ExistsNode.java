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
	protected void translate(StringBuffer buffer, GoalContext context) {
		if (obj.getType(context) != ObjectNode.TERM)
			throw new RuntimeException("ExistsNode: the argument must be TERM");
		
		buffer.append('(');
		buffer.append("exists_tac ");
		obj.translate(buffer, context);
		buffer.append(')');
	}
}
