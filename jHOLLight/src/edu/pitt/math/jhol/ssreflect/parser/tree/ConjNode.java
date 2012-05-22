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
	protected int getType() {
		return THEOREM;
	}

	@Override
	protected void translate(StringBuffer buffer) {
		int type1 = th1.getType();
		int type2 = th2.getType();
		if ((type1 != THEOREM && type1 != UNKNOWN) ||
			(type2 != THEOREM && type2 != UNKNOWN))
			throw new RuntimeException("ConjNode: THEOREM expected");
		
		buffer.append("(fun arg_tac ->");
		th1.translate(buffer);
		buffer.append("(fun tmp_arg1 -> ");
		th2.translate(buffer);
		
		buffer.append("(fun tmp_arg2 -> arg_tac (Arg_theorem (CONJ (get_arg_thm tmp_arg1) (get_arg_thm tmp_arg2))))");
		buffer.append(')');
		buffer.append(')');
	}

	@Override
	protected boolean isWildCard() {
		return false;
	}

}
