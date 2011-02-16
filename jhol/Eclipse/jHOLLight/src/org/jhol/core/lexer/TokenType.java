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
	COMMA, COLON, SEMICOLON,
	Tyapp, Tyvar,
	Var, Const, Comb, Abs,
	String, HOLType, Term, Theorem, List, Pair,
	Goal, Goalstate
}
