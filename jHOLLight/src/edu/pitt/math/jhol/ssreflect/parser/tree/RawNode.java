package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * Purely raw command
 */
public class RawNode extends TacticNode {
	// Raw text
	private final String rawText;
	
	/**
	 * Default constructor 
	 */
	public RawNode(String rawText) {
		assert(rawText != null);
		this.rawText = rawText;
	}

	@Override
	protected String getString() {
		return "{" + rawText + "}";
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append(rawText);
	}
	
}
