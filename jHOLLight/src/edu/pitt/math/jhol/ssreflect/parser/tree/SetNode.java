package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * set f := term
 */
public class SetNode extends TacticNode {
	// The identifier
	private final IdNode id;
	// The value
	private final ObjectNode value;
	
	/**
	 * Default constructor
	 */
	public SetNode(IdNode id, ObjectNode value) {
		assert(id != null);
		assert(value != null);
	
		this.id = id;
		this.value = value;
	}

	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder();
		str.append("set ");
		str.append(id);
		str.append(" := ");
		str.append(value);

		return str.toString();
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		buffer.append('(');
		
		String name = id.getId();
		buffer.append("set_tac ");
		buffer.append('"' + name + '"');
		buffer.append(' ');
		value.translate(buffer, context);
		
		buffer.append(')');
	}
	
}
