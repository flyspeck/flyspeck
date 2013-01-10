package edu.pitt.math.jhol.core.parser;

/**
 * Token type
 */
enum TokenType {
	EOF,
	STRING, IDENTIFIER, INTEGER,
	LPAR, RPAR,
	LBRACK, RBRACK,
	COMMA, COLON, SEMICOLON,
	False, True,
	Tyapp, Tyvar,
	Var, Const, Comb, Abs,
	String, Int, HOLType, Term, Theorem, List, Pair,
	Goal, Goalstate
}
