package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * An application node
 */
public class ApplicationNode extends ObjectNode {
	// The first object
	private final ObjectNode firstObject;
	// Argument
	private final ObjectNode argument;
	
	/**
	 * Default constructor
	 * @param firstObject
	 */
	public ApplicationNode(ObjectNode firstObject, ObjectNode argument) {
		assert(firstObject != null);
		assert(argument != null);

		this.firstObject = firstObject;
		this.argument = argument;
	}
	
	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder();
		str.append("(");
		str.append(firstObject);
		
		str.append(" ");
		str.append(argument);
		
		str.append(")");
		
		return str.toString();
	}

	@Override
	protected int getType(GoalContext context) {
		return THEOREM;
	}

	// Translates the first object
	private void translateFirst(StringBuffer buffer, GoalContext context) {
		if (firstObject instanceof WildObjectNode) {
			// WildCard
			buffer.append("DISCH_THEN ");
		}
		else {
			// Normal object
			firstObject.translate(buffer, context);
		}
	}

	@Override
	protected void translate(StringBuffer buffer, GoalContext context) {
		int firstType = firstObject.getType(context);
		if (firstType != THEOREM && firstType != UNKNOWN)
			throw new RuntimeException("Applications work for theorems only: " + firstObject);
		
		buffer.append('(');
		buffer.append("fun thm_tac -> ");
		translateFirst(buffer, context);
		
		buffer.append('(');
		int argType = argument.getType(context);
		
		if (argType == TERM) {
			// ISPEC_THEN
			buffer.append("ispec_then ");
			argument.translate(buffer, context);
			buffer.append(" thm_tac");
		}
		else if (argType == TYPE) {
			// inst_first_type
			buffer.append("INST_FIRST_TYPE_THEN ");
			argument.translate(buffer, context);
			buffer.append(" thm_tac");
		}
		else {
			// MATCH_MP_THEN
			buffer.append("fun fst_th ->");
			argument.translate(buffer, context);
			buffer.append("(fun th -> match_mp_then th thm_tac fst_th)");
		}
		
		buffer.append(')');
		
		buffer.append(')');
	}

	@Override
	protected boolean isWildCard() {
		return firstObject.isWildCard();
	}

	@Override
	protected void setWildCardInterpretation(String interpretation) {
		firstObject.setWildCardInterpretation(interpretation);
	}
	
}
