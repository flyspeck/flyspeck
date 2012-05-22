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

	/**
	 * Default constructor
	 */
	public LemmaNode(String name, String[] params, RawObjectNode goal) {
		assert(name != null && name.length() > 0);
		assert(goal != null);
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
	 * Returns the text description of the goal
	 */
	public String getGoalText() {
		return goal.getRawText();
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

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		buffer.append("start_section_proof ");
		
		buffer.append('[');
		for (int i = 0; i < params.length; i++) {
			buffer.append('"' + params[i] + '"');
			if (i < params.length - 1)
				buffer.append(';');
		}
		buffer.append(']');
		
		goal.directTranslate(buffer);
		buffer.append(')');
	}
	
	
	@Override
	public String getRevertCommand() {
//		return "let " + name + " = 0"; 
		// TODO: undefine the theorem if possible
		return null;
	}
}
