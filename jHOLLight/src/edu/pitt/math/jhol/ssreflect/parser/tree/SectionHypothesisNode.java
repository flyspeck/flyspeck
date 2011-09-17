package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * A section hypothesis
 */
public class SectionHypothesisNode extends Node {
	// The label
	private final String label;
	// The term
	private final ObjectNode term;

	/**
	 * Constructor
	 */
	public SectionHypothesisNode(String label, ObjectNode term) {
		assert(label != null);
		assert(term != null);
		this.label = label;
		this.term = term;
	}
	
	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		term.beginTranslation(buffer, context);
		if (term.getType() != ObjectNode.TERM)
			throw new RuntimeException("TERM expected: " + term);
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		term.endTranslation(buffer);
	}

	@Override
	protected String getString() {
		return "Hypothesis " + label + " : " + term;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		buffer.append("add_section_hyp ");
		
		buffer.append('"' + label + '"');
		buffer.append(' ');
		term.translate(buffer);
		
		buffer.append(')');
	}

}
