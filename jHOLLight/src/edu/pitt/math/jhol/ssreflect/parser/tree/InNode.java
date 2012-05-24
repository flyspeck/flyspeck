package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;

/**
 * tac in id+ [*]
 */
public class InNode extends TacticNode {
	// Tactic
	private final TacticNode thenTactic;
	// Identifiers
	private final ArrayList<String> ids;
	// If true then the tactic is applied to the goal
	private final boolean goalFlag;
	
	/**
	 * Default constructor
	 */
	public InNode(TacticNode thenTactic, ArrayList<String> ids, boolean goalFlag) {
		assert(thenTactic != null);

		this.thenTactic = thenTactic;
		this.ids = new ArrayList<String>();
		this.goalFlag = goalFlag;
		
		if (ids != null)
			this.ids.addAll(ids);
	}

	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder();
		str.append(thenTactic);
		str.append(" in ");
		str.append(ids);
		
		return str.toString();
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append('(');
		buffer.append("in_tac ");
		
		// ids
		int n = ids.size();
		buffer.append('[');
			
		for (int i = 0; i < n; i++) {
			buffer.append('"');
			buffer.append(ids.get(i));
			buffer.append('"');
			if (i < n - 1)
				buffer.append("; ");
		}
			
		buffer.append(']');
		
		// goal
		if (goalFlag)
			buffer.append(" true ");
		else
			buffer.append(" false ");

		// tactic
		thenTactic.translate(buffer);
			
		buffer.append(')');
	}
	
}
