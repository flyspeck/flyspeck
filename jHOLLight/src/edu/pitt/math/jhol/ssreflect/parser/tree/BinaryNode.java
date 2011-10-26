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
	protected String getString() {
		return tactic.toString() + ": " + left + ", " + right;
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		buffer.append('(');
		tactic.translate(buffer, context);
		buffer.append(' ');
		left.translate(buffer, context);
		
		if (right != null) {
			buffer.append(' ');
			right.translate(buffer, context);
		}
		
		buffer.append(')');
	}

}
