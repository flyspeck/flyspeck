package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;

/**
 * move: x
 */
public class DischNode extends TacticNode {
	// Specifies which terms must be generalized
	private final ArrayList<Integer> occs;
	// The object which is discharged
	private final ObjectNode obj;
	
	/**
	 * Default constructor
	 */
	public DischNode(ObjectNode obj, ArrayList<Integer> occs) {
		assert(obj != null);
		this.obj = obj;
		if (occs == null)
			this.occs = new ArrayList<Integer>();
		else
			this.occs = new ArrayList<Integer>(occs);
	}

	@Override
	protected String getString() {
		return "disch " + obj;
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		buffer.append('(');
		
		int type = obj.getType(context);
		if (type == ObjectNode.TERM) {
			// term: disch_tm_tac
			buffer.append("disch_tm_tac ");
			
			// occs
			buffer.append('[');
			int n = occs.size();
			for (int i = 0; i < n; i++) {
				buffer.append(occs.get(i));
				if (i < n - 1)
					buffer.append("; ");
			}
			buffer.append(']');
			
			// tm
			obj.translate(buffer, context);
		}
		else {
			// theorem: MP_TAC
			obj.translate(buffer, context);
			buffer.append("MP_TAC");
		}
		
		buffer.append(')');
	}
}
