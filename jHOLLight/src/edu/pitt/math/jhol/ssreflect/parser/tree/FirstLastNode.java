package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * first tactic
 * last tactic
 */
public class FirstLastNode extends LeftAssociativeTacticNode {
	// If true then 'first tactic' else 'last tactic'
	private boolean firstFlag;
	// Tactic
	private TacticNode tactic;
	
	/**
	 * Default constructor
	 */
	public FirstLastNode(boolean firstFlag, TacticNode tactic) {
		assert (tactic != null);
		this.firstFlag = firstFlag;
		this.tactic = tactic;
	}
	
	@Override
	protected String getString() {
		if (firstFlag)
			return "first " + tactic;
		else
			return "last " + tactic;
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		// This method should be never called
		throw new Error("FirstLastNode.translate()");
	}
	
	@Override
	public TacticNode transformTactic(TacticChainNode left) {
		TacticNode tac = new RawTactic(firstFlag ? "THENL_FIRST" : "THENL_LAST");
		return new BinaryNode(tac, left, tactic);
	}
	
}
