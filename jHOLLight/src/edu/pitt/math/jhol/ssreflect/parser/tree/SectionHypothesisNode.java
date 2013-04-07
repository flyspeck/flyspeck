package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * A section hypothesis
 */
public class SectionHypothesisNode extends Node {
	// The label
	private final String label;
	// The term
	private final RawObjectNode term;

	/**
	 * Constructor
	 */
	public SectionHypothesisNode(String label, RawObjectNode term) {
		assert(label != null);
		assert(term != null);
		this.label = label;
		this.term = term;
	}
	
	@Override
	protected String getString() {
		return "Hypothesis " + label + " : " + term;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		int type = term.getType();
		if (type != ObjectNode.TERM && type != ObjectNode.UNKNOWN)
			throw new RuntimeException("TERM expected: " + term);

		buffer.append('(');
		buffer.append("Sections.add_section_hyp ");
		
		buffer.append('"' + label + '"');
		buffer.append(' ');
		term.directTranslate(buffer);
		
		buffer.append(')');
	}
	
	
	@Override
	public String getRevertCommand() {
		return "Sections.remove_section_hyp " + '"' + label + '"';
	}

}
