package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * _
 */
public class WildObjectNode extends ObjectNode {
	// Interpretation of this wild card
	private String wildCardInterpretation;
	
	/**
	 * Default constructor
	 */
	public WildObjectNode() {
	}
	
	/**
	 * Returns the interpretation of this wild card
	 */
	public String getInterpretation() {
		return wildCardInterpretation;
	}

	@Override
	protected void setWildCardInterpretation(String interpretation) {
		this.wildCardInterpretation = interpretation;
	}
	
	@Override
	protected String getString() {
		return "_";
	}

	@Override
	protected int getType() {
		return UNKNOWN;
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
	}

	@Override
	protected void translate(StringBuffer buffer) {
		// TODO Auto-generated method stub
		throw new RuntimeException("wildcard.translate(): unimplemented");
		
	}

	@Override
	protected boolean isWildCard() {
		return true;
	}

}
