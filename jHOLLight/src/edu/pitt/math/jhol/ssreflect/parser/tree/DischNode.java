package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * move => x
 */
public class DischNode extends TacticNode {
	// The label of the discharged object 
	private final IdNode id;
	
	/**
	 * Default constructor
	 */
	public DischNode(IdNode id) {
		assert(id != null);
		this.id = id;
	}

	@Override
	protected String getString() {
		return "disch " + id;
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		// TODO: check if the id is not defined in the context
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		// Do nothing here
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append("(move [\"" + id.getId() + "\"])");
	}
}
