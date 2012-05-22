package edu.pitt.math.jhol.ssreflect.parser.tree;

/**
 * A raw HOL Light object
 */
public class RawObjectNode extends ObjectNode {
	// Raw text
	private final String rawText;
	// True if the raw object is definitely a term 
	private final int type;
	
	/**
	 * Default constructor 
	 */
	public RawObjectNode(String rawText) {
		assert(rawText != null);
		assert(rawText.length() > 0);
		
		int n = rawText.length();
		if (rawText.charAt(0) == '`') {
			// Determine the type of the raw expression
			if (n >= 2 && rawText.charAt(1) == ':')
				type = TYPE;
			else
				type = TERM;
			
			// Add closing '`' if necessary
			if (n == 1 || rawText.charAt(n - 1) != '`')
				rawText += '`';
		}
		else {
			type = UNKNOWN;
		}
		
		this.rawText = rawText;
	}
	
	/**
	 * Returns the raw text
	 */
	public String getRawText() {
		return rawText;
	}

	@Override
	protected String getString() {
		return "{" + rawText + "}";
	}

	@Override
	protected int getType() {
		return type;
	}
	
	/**
	 * Directly inserts the raw text into the buffer 
	 */
	public void directTranslate(StringBuffer buffer) {
		buffer.append('(');
		buffer.append(rawText);
		buffer.append(')');
	}

	@Override
	protected void translate(StringBuffer buffer) {
		buffer.append("(fun arg_tac -> arg_tac (");

		if (type == TERM)
			buffer.append("Arg_term (");
		else if (type == TYPE)
			buffer.append("Arg_type (");
		else
			buffer.append("Arg_theorem (");
		
		buffer.append(rawText);
		buffer.append(")))");
	}

	@Override
	protected boolean isWildCard() {
		return false;
	}

}
