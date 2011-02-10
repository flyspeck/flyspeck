package org.jhol.core.lexer;

/**
 * Token type
 */
public enum TokenType {
	EOF,
	STRING,
	IDENTIFIER,
	LPAR, RPAR,
	LBRACK, RBRACK,
	COMMA,
	Tyapp, Tyvar,
	Var, Const, Comb, Abs
}
