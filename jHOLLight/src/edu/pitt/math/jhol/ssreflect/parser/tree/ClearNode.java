package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * Clears the given assumption
 */
public class ClearNode extends TacticNode {
	// The object which is cleared
	private final IdNode id;
	
	/**
	 * Default constructor
	 */
	public ClearNode(IdNode id) {
		assert(id != null);
		this.id = id;
	}

	@Override
	protected String getString() {
		return "clear " + id;
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		buffer.append('(');
		buffer.append("clear_assumption ");
		buffer.append('"');
		buffer.append(id.getId());
		buffer.append('"');
		buffer.append(')');
	}
}

