package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * A conjunction of two theorems
 */
public class ConjNode extends ObjectNode {
	// Two theorems
	private final ObjectNode th1, th2; 
	
	/**
	 * Default constructor 
	 */
	public ConjNode(ObjectNode th1, ObjectNode th2) {
		assert(th1 != null && th2 != null);
		this.th1 = th1;
		this.th2 = th2;
	}
	

	@Override
	protected String getString() {
		return "(" + th1 + ", " + th2 + ")";
	}

	@Override
	protected int getType(GoalContext context) {
		return THEOREM;
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		int type1 = th1.getType(context);
		int type2 = th2.getType(context);
		if ((type1 != THEOREM && type1 != UNKNOWN) ||
			(type2 != THEOREM && type2 != UNKNOWN))
			throw new RuntimeException("ConjNode: THEOREM expected");
		
		buffer.append("(fun thm_tac ->");
		th1.translate(buffer,context);
		buffer.append("(fun tmp_th1 -> ");
		th2.translate(buffer, context);
		
		buffer.append("(fun tmp_th2 -> thm_tac (CONJ tmp_th1 tmp_th2))");
		buffer.append(')');
		buffer.append(')');
	}

	@Override
	protected boolean isWildCard() {
		return false;
	}

}
