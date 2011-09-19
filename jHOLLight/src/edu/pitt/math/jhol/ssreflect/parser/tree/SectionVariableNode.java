package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;

/**
 * A section variable
 */
public class SectionVariableNode extends Node {
	// The name
	private final ArrayList<String> names;
	// The type
	private final RawObjectNode type;

	/**
	 * Constructor
	 */
	public SectionVariableNode(ArrayList<String> names, RawObjectNode type) {
		assert(names != null);
		assert(type != null);
		this.names = names;
		this.type = type;
	}
	
	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		type.beginTranslation(buffer, context);
		if (type.getType() != ObjectNode.TYPE)
			throw new RuntimeException("TYPE expected: " + type);
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		type.endTranslation(buffer);
	}

	@Override
	protected String getString() {
		StringBuffer str = new StringBuffer("Variable ");
		for (String name : names) {
			str.append(name);
			str.append(' ');
		}
		
		str.append(": ");
		str.append(type);
		
		return str.toString();
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		int n = names.size();
		
		for (int i = 0; i < n; i++) {
			String name = names.get(i);
			buffer.append("add_section_var ");

			buffer.append("(mk_var (\"");
			buffer.append(name);
			buffer.append("\", ");
			type.translate(buffer);
			buffer.append("))");
			
			if (i < n - 1)
				buffer.append("; ");
		}
		
		buffer.append(')');
	}

	@Override
	public String getRevertCommand() {
		StringBuffer str = new StringBuffer();
		int n = names.size();
		
		for (int i = 0; i < n; i++) {
			String name = names.get(i);
			str.append("remove_section_var ");
			str.append('"' + name + '"');
			
			if (i < n - 1)
				str.append("; ");
		}
		
		return str.toString();
	}
}
