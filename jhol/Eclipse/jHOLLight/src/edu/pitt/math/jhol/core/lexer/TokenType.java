package edu.pitt.math.jhol.core.lexer;

/**
 * Token type
 */
public enum TokenType {
	EOF,
	STRING, IDENTIFIER, INTEGER,
	LPAR, RPAR,
	LBRACK, RBRACK,
	COMMA, COLON, SEMICOLON,
	Tyapp, Tyvar,
	Var, Const, Comb, Abs,
	String, Int, HOLType, Term, Theorem, List, Pair,
	Goal, Goalstate
}
