package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * A tactic node with two (or one) arguments
 * @author monad
 *
 */
public class BinaryNode extends TacticNode {
	// The main tactic
	private final TacticNode tactic;
	// Arguments
	private final TacticNode left, right;

	/**
	 * Constructor
	 */
	public BinaryNode(TacticNode tactic, TacticNode left, TacticNode right) {
		assert(tactic != null && left != null);
		
		this.tactic = tactic;
		this.left = left;
		this.right = right;
	}
	
	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		tactic.beginTranslation(buffer, context);
		left.beginTranslation(buffer, context);
		if (right != null)
			right.beginTranslation(buffer, context);
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		if (right != null)
			right.endTranslation(buffer);
		left.endTranslation(buffer);
		tactic.endTranslation(buffer);
	}

	@Override
	protected String getString() {
		return tactic.toString() + ": " + left + ", " + right;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		tactic.translate(buffer);
		buffer.append(' ');
		left.translate(buffer);
		
		if (right != null) {
			buffer.append(' ');
			right.translate(buffer);
		}
		
		buffer.append(')');
	}

}
