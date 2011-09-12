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
		throw new RuntimeException("Unimplemented");
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		throw new RuntimeException("Unimplemented");
	}

	@Override
	protected void translate(StringBuffer buffer) {
		throw new RuntimeException("Unimplemented");
	}
}
