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
		// Argument could be null
		this.firstObject = firstObject;
		this.argument = argument;
	}
	
	@Override
	protected String getString() {
		StringBuilder str = new StringBuilder();
		str.append("(");
		str.append(firstObject);
		
		if (argument != null) {
			str.append(" ");
			str.append(argument);
		}
		
		str.append(")");
		
		return str.toString();
	}

	@Override
	protected int getType() {
		// Applications with arguments are considered to be theorems
		if (argument != null)
			return THEOREM;
		
		return firstObject.getType();
	}

	@Override
	protected void beginTranslation(StringBuffer buffer, GoalContext context) {
		firstObject.beginTranslation(buffer, context);
		if (argument != null)
			argument.beginTranslation(buffer, context);
	}

	@Override
	protected void endTranslation(StringBuffer buffer) {
		if (argument != null)
			argument.endTranslation(buffer);
		firstObject.endTranslation(buffer);
	}
	
	// Translates the first object
	private void translateFirst(StringBuffer buffer) {
		if (firstObject instanceof WildObjectNode) {
			// WildCard
			WildObjectNode wildCard = (WildObjectNode) firstObject;
			String interpretation = wildCard.getInterpretation();
			if (interpretation == null)
				throw new RuntimeException("Wildcard without interpretation");
			buffer.append(interpretation);
		}
		else {
			// Normal object
			firstObject.translate(buffer);
		}
	}

	@Override
	protected void translate(StringBuffer buffer) {
		if (argument == null) {
			translateFirst(buffer);
			return;
		}
		
		buffer.append("(");
		// argument != null
		int argType = argument.getType();
		
		if (argType == TERM) {
			// ISPEC
			buffer.append("ISPEC ");
			argument.translate(buffer);
			buffer.append(' ');
			translateFirst(buffer);
		}
		else if (argType == TYPE) {
			// inst_first_type
			buffer.append("inst_first_type ");
			argument.translate(buffer);
			buffer.append(' ');
			translateFirst(buffer);
		}
		else {
			// MATCH_MP
			buffer.append("MATCH_MP ");
			translateFirst(buffer);
			buffer.append(" ");
			argument.translate(buffer);
		}
		
		buffer.append(")");
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
