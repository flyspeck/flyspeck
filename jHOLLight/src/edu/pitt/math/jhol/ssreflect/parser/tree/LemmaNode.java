package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * Describes a lemma
 */
public class LemmaNode extends Node {
	// Lemma's name
	private final String name;
	// Lemma's goal
	private final RawObjectNode goal; 

	/**
	 * Default constructor
	 */
	public LemmaNode(String name, RawObjectNode goal) {
		assert(name != null && name.length() > 0);
		assert(goal != null);
		this.name = name;
		this.goal = goal;
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
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
	}

	@Override
	protected String getString() {
		return "Lemma " + name + ": " + goal;
	}

	@Override
	protected void translate(StringBuffer buffer) {
	}
}
