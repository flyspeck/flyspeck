package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;

/**
 * A chain of tactics
 */
public class TacticChainNode extends TacticNode {
	// A list of all tactics in the chain
	protected ArrayList<TacticNode> tactics = new ArrayList<TacticNode>();

	/**
	 * Default constructor
	 */
	public TacticChainNode() {
	}
	
	/**
	 * Adds a tactics to the chain
	 * @param tactic
	 */
	public void add(TacticNode tactic) {
		if (tactic == null)
			return;

		tactics.add(tactic);
	}
	
	/**
	 * Returns the number of tactics in the chain
	 */
	public int size() {
		return tactics.size();
	}
	
	/**
	 * Returns true if the chain contains nothing or other empty chains
	 */
	public boolean isEmpty() {
		for (TacticNode tactic : tactics) {
			if (tactic instanceof TacticChainNode) {
				if (!((TacticChainNode) tactic).isEmpty())
					return false;
			}
			else {
				return false;
			}
		}
		
		return true;
	}
	
	@Override
	public boolean isParallel() {
		if (tactics.size() > 0)
			return tactics.get(0).isParallel();
		
		return false;
	}
	
	/**
	 * Returns the i-th tactic in the chain
	 */
	public TacticNode get(int i) {
		return tactics.get(i);
	}

	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder();
		str.append('(');

		int n = size();
		for (int i = 0; i < n; i++) {
			TacticNode tac = tactics.get(i);
			str.append(tac);
			if (i < n - 1)
				str.append(" THEN ");
		}
		
		str.append(')');
		
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
		
		boolean parFlag = true;
		if (n == 1) {
			if (tactics.get(0) instanceof TacticChainNode)
				parFlag = false;
		}
		
		if (parFlag)
			buffer.append('(');
		for (int i = 0; i < n; i++) {
			tactics.get(i).translate(buffer);
			if (i < n - 1) {
				if (tactics.get(i + 1).isParallel())
					buffer.append(" THENL ");
				else
					buffer.append(" THEN ");
			}
		}
		
		if (parFlag)
			buffer.append(')');
	}
}
