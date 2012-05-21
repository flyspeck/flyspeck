package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;

/**
 * A set of parallel tactics
 */
public class TacticParallelNode extends LeftAssociativeTacticNode {
	// A list of all tactics
	private ArrayList<TacticChainNode> tactics = new ArrayList<TacticChainNode>();

	/**
	 * Default constructor
	 */
	public TacticParallelNode() {
	}
	
	public TacticParallelNode(TacticChainNode tac) {
		add(tac);
	}
	
	/**
	 * Adds a tactics to the set
	 * @param tactic
	 */
	public void add(TacticChainNode tactic) {
		if (tactic == null)
			return;

		tactics.add(tactic);
	}
	
	/**
	 * Returns the number of tactics in the set
	 */
	public int size() {
		return tactics.size();
	}
	
	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder();
		str.append('[');

		int n = size();
		for (int i = 0; i < n; i++) {
			TacticNode tac = tactics.get(i);
			str.append(tac);
			if (i < n - 1)
				str.append(" | ");
		}
		
		str.append(']');
		
		return str.toString();
	}
	
	@Override
	public TacticNode transformTactic(TacticChainNode left) {
		if (size() == 0)
			return left;
		
		if (size() == 1) {
			left.add(tactics.get(0));
			return left;
		}
		
		TacticNode thenl = new RawTactic("(THENL)");
		return new BinaryNode(thenl, left, this);
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		int n = size();
		if (n == 0) {
			buffer.append("ALL_TAC");
			return;
		}
		
		if (n == 1) {
			tactics.get(0).translate(buffer, context);
			return;
		}

		buffer.append('[');
		
		for (int i = 0; i < n; i++) {
			tactics.get(i).translate(buffer, context);
			if (i < n - 1) {
				buffer.append("; ");
			}
		}
		
		buffer.append(']');
	}
}
