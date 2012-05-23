package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * congr `term`
 */
public class CongrNode extends TacticNode {
	// The pattern
	private final RawObjectNode pattern;
	
	/**
	 * Default constructor
	 */
	public CongrNode(RawObjectNode pattern) {
		assert(pattern != null);
		this.pattern = pattern;
	}

	@Override
	protected String getString() {
		return "congr " + pattern;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		if (pattern.getType() != ObjectNode.TERM)
			throw new RuntimeException("TERM expected: " + pattern);
		
		buffer.append("(congr_tac ");
		pattern.directTranslate(buffer);
		buffer.append(')');
	}
	
}
