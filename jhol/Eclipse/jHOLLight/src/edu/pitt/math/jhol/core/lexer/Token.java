package edu.pitt.math.jhol.core.lexer;


/**
 * Token
 * @author Alexey
 */
public class Token {
	// Type
	public final TokenType type;
	
	// Value
	public final String value;

	/**
	 * Default constructor
	 */
	public Token(TokenType type, String value) {
		this.type = type;
		this.value = value;
	}
	
	public Token(TokenType type) {
		this(type, null);
	}
	
	@Override
	public String toString() {
		String str = type.toString();
		str += '[';
		if (value != null)
			str += value;
		str += ']';
		
		return str;
	}
}