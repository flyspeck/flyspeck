package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * Describes a module
 */
public class ModuleNode extends Node {
	// Module's name
	private final String name;

	/**
	 * Default constructor
	 */
	public ModuleNode(String name) throws Exception {
		assert(name != null && name.length() > 0);
		
		// Ensure that the module name is acceptable
		String tmp = name.substring(0, 1).toUpperCase() + name.substring(1).toLowerCase();
		if (!tmp.equals(name))
			throw new Exception("Bad module name:" + name + " (the name should be " + tmp + ")");
		
		this.name = name;
	}
	
	/**
	 * Returns the name of the module
	 */
	public String getName() {
		return name;
	}
	
	@Override
	protected String getString() {
		return "Module " + name;
	}
	
	@Override
	protected void translate(StringBuffer buffer) {
		// Do nothing here.
		// The module command is translated during the compilation stage only.
		buffer.append("()");
	}
	
	
	@Override
	public String getRevertCommand() {
		return null;
	}
}
