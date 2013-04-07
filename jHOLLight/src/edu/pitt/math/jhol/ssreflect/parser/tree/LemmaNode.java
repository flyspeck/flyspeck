package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * Describes a lemma
 */
public class LemmaNode extends Node {
	// Lemma's name
	private final String name;
	// Lemma's parameters
	private final String[] params;
	// Lemma's goal
	private final RawObjectNode goal; 
	// True for local section lemmas
	private final boolean letFlag;

	/**
	 * Default constructor
	 */
	public LemmaNode(boolean letFlag, String name, String[] params, RawObjectNode goal) {
		assert(name != null && name.length() > 0);
		assert(goal != null);
		this.letFlag = letFlag;
		this.name = name;
		this.goal = goal;
		this.params = (params == null) ? new String[0] : params.clone();
	}
	
	/**
	 * Returns the name
	 */
	public String getName() {
		return name;
	}
	
	/**
	 * Returns parameters
	 */
	public String[] getParameters() {
		return params;
	}
	
	/**
	 * Returns the text description of the goal
	 */
	public String getGoalText() {
		return goal.getRawText();
	}
	
	/**
	 * Returns true if the lemma is a local section lemma
	 */
	public boolean isLet() {
		return letFlag;
	}
	
	@Override
	protected String getString() {
		StringBuffer str = new StringBuffer("Lemma ");
		str.append(name + ' ');
		
		for (String p : params) {
			str.append(p);
			str.append(' ');
		}
		
		str.append(": ");
		str.append(goal);
		
		return str.toString();
	}
	
	/**
	 * Translates lemma's parameters
	 */
	public void translateParameters(StringBuffer buffer) {
		buffer.append('[');
		for (int i = 0; i < params.length; i++) {
			buffer.append('"' + params[i] + '"');
			if (i < params.length - 1)
				buffer.append(';');
		}
		buffer.append(']');
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		
		buffer.append("Sections.start_section_proof ");
		translateParameters(buffer);
		goal.directTranslate(buffer);

		buffer.append(')');
	}
	
	
	@Override
	public String getRevertCommand() {
		if (letFlag) {
			return "Sections.remove_section_lemma " + '"' + name + '"';
		}
		else {
			return "let " + name + " = 0";
		}
	}
}
