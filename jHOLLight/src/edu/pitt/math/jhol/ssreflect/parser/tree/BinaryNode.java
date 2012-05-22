package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * A tactic node with two (or one) arguments
 * @author monad
 *
 */
public class BinaryNode extends TacticNode {
	// If true then a translated expression will be in the form (left tactic right)
	private final boolean infix;
	// The main tactic
	private final TacticNode tactic;
	// Arguments
	private final TacticNode left, right;

	/**
	 * Constructor
	 */
	public BinaryNode(boolean infix, TacticNode tactic, TacticNode left, TacticNode right) {
		assert(tactic != null && left != null);
		
		this.infix = infix;
		this.tactic = tactic;
		this.left = left;
		this.right = right;
	}
	

	@Override
	protected String getString() {
		return tactic.toString() + ": " + left + ", " + right;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		TacticNode first, second;
		
		if (infix) {
			first = left;
			second = tactic;
		}
		else {
			first = tactic;
			second = left;
		}
		
		buffer.append('(');

		first.translate(buffer);
		buffer.append(' ');
		second.translate(buffer);
		
		if (right != null) {
			buffer.append(' ');
			right.translate(buffer);
		}
		
		buffer.append(')');
	}

}
