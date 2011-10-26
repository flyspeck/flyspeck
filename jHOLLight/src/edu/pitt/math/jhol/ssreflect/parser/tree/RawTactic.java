package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * {HOL Light tactics} 
 */
public class RawTactic extends TacticNode {
	// Raw text
	private final String rawText;
	
	/**
	 * Default constructor 
	 */
	public RawTactic(String rawText) {
		assert(rawText != null);
		this.rawText = rawText;
	}

	@Override
	protected String getString() {
		return "{" + rawText + "}";
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		buffer.append("(" + rawText + ")");
	}
	
}
