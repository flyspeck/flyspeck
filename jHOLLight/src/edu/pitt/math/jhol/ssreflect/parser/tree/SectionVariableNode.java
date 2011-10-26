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
	// Implicit type (not a variable)
	private final boolean implicitTypeFlag;

	/**
	 * Constructor
	 */
	public SectionVariableNode(ArrayList<String> names, RawObjectNode type, boolean implicitType) {
		assert(names != null);
		assert(type != null);
		this.names = names;
		this.type = type;
		this.implicitTypeFlag = implicitType;
	}
	
	@Override
	protected String getString() {
		StringBuffer str = new StringBuffer();
		if (implicitTypeFlag)
			str.append("Implicit Type ");
		else
			str.append("Variable ");
		
		for (String name : names) {
			str.append(name);
			str.append(' ');
		}
		
		str.append(": ");
		str.append(type);
		
		return str.toString();
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		int ty = type.getType(context);
		if (ty != ObjectNode.TYPE)
			throw new RuntimeException("TYPE expected: " + type);

		buffer.append('(');
		int n = names.size();
		
		for (int i = 0; i < n; i++) {
			String name = names.get(i);
			if (implicitTypeFlag)
				buffer.append("add_section_type ");
			else
				buffer.append("add_section_var ");

			buffer.append("(mk_var (\"");
			buffer.append(name);
			buffer.append("\", ");
			type.translate(buffer, context);
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
			if (implicitTypeFlag)
				str.append("remove_section_type ");
			else
				str.append("remove_section_var ");
			str.append('"' + name + '"');
			
			if (i < n - 1)
				str.append("; ");
		}
		
		return str.toString();
	}
}
