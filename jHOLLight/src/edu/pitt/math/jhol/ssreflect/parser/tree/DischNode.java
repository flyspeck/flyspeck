package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * move => x
 */
public class DischNode extends TacticNode {
	// The label of the discharged object 
	private final ObjectNode id;
	
	/**
	 * Default constructor
	 */
	public DischNode(ObjectNode id) {
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
		String name = null;
		// IdNode
		if (id instanceof IdNode) {
			name = ((IdNode) id).getId();
		}
		// _
		else if (id instanceof WildObjectNode) {
			name = "_";
		}
		
		if (name == null)
			throw new RuntimeException("DischNode.translate(): id must be IdNode or WildObjectNode");
		
		buffer.append("(move [\"" + name + "\"])");
	}
}
