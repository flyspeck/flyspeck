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
	protected int getType() {
		return THEOREM;
	}

	// Translates the first object
	private void translateFirst(StringBuffer buffer) {
		if (firstObject instanceof WildObjectNode) {
			// WildCard
			buffer.append(" (conv_thm_tac DISCH_THEN) ");
		}
		else {
			// Normal object
			firstObject.translate(buffer);
		}
	}

	@Override
	protected void translate(StringBuffer buffer) {
		int firstType = firstObject.getType();
		if (firstType != THEOREM && firstType != UNKNOWN)
			throw new RuntimeException("Applications work for theorems only: " + firstObject);
		
		buffer.append("(fun arg_tac -> ");
		translateFirst(buffer);
		buffer.append(" (fun fst_arg -> ");
		argument.translate(buffer);
		buffer.append(" (fun snd_arg -> combine_args_then arg_tac fst_arg snd_arg)");
		buffer.append("))");
	}

	@Override
	protected boolean isWildCard() {
		return firstObject.isWildCard();
	}

}
