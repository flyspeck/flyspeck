package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * A section variable
 */
public class SectionVariableNode extends Node {
	// The name
	private final String name;
	// The type
	private final RawObjectNode type;

	/**
	 * Constructor
	 */
	public SectionVariableNode(String name, RawObjectNode type) {
		assert(name != null);
		assert(type != null);
		this.name = name;
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
		return "Variable " + name + " : " + type;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		buffer.append("add_section_var ");
		
		buffer.append("(mk_var (\"");
		buffer.append(name);
		buffer.append("\", ");
		type.translate(buffer);
		buffer.append("))");
		
		buffer.append(')');
	}

}
