package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * move => x
 */
public class IntroductionNode extends TacticNode {
	// The label of the introduced object 
	private final ObjectNode id;
	
	/**
	 * Default constructor
	 */
	public IntroductionNode(ObjectNode id) {
		assert(id != null);
		this.id = id;
	}

	@Override
	protected String getString() {
		return "intro " + id;
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
			throw new RuntimeException("IntroductionNode.translate(): id must be IdNode or WildObjectNode");
		
		buffer.append("(move [\"" + name + "\"])");
	}
}
