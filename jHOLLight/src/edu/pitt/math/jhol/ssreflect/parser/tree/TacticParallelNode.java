package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;

/**
 * A set of parallel tactics
 */
public class TacticParallelNode extends TacticNode {
	// A list of all tactics
	protected ArrayList<TacticNode> tactics = new ArrayList<TacticNode>();

	/**
	 * Default constructor
	 */
	public TacticParallelNode() {
	}
	
	public TacticParallelNode(TacticNode tac) {
		add(tac);
	}
	
	/**
	 * Adds a tactics to the set
	 * @param tactic
	 */
	public void add(TacticNode tactic) {
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
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		for (TacticNode tac : tactics) {
			tac.beginTranslation(buffer, context);
		}
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		int n = size();
		for (int i = n - 1; i >= 0; i--) {
			tactics.get(i).endTranslation(buffer);
		}
	}

	@Override
	protected void translate(StringBuffer buffer) {
		int n = size();
		if (n == 0) {
			buffer.append("ALL_TAC");
			return;
		}
		
		if (n == 1) {
			tactics.get(0).translate(buffer);
			return;
		}

		buffer.append('[');
//		buffer.append("ALL_TAC THENL [");
		
		for (int i = 0; i < n; i++) {
			tactics.get(i).translate(buffer);
			if (i < n - 1) {
				buffer.append("; ");
			}
		}
		
		buffer.append(']');
//		buffer.append(')');
	}
	
	@Override
	public boolean isParallel() {
		return tactics.size() > 1;
	}
}
