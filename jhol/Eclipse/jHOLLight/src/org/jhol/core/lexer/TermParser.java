package org.jhol.core.lexer;

import java.io.StringReader;
import java.util.ArrayList;

import org.jhol.core.HOLType;
import org.jhol.core.Term;

/**
 * Parses HOL terms and types
 * @author Alexey
 */
public class TermParser {
	/**
	 * Parses a HOL type
	 */
	public static HOLType parseType(Scanner s) throws Exception {
		Token t = s.peekToken();
		
		switch (t.type) {
		case Tyapp:
			return parseTyapp(s);
		case Tyvar:
			return parseTyvar(s);
		}

		throw new Exception("Tyapp | Tyvar expected: " + t);
	}
	
	
	/**
	 * Parses a term
	 */
	public static Term parseTerm(Scanner s) throws Exception {
		Token t = s.peekToken();
		
		switch (t.type) {
		case Var:
			return parseVar(s);
		case Const:
			return parseConst(s);
		case Comb:
			return parseComb(s);
		case Abs:
			return parseAbs(s);
		}
		
		throw new Exception("Var | Const | Comb | Abs expected: " + t);
	}
	
	
	/**
	 * Creates a term from a raw string description
	 */
	public final static Term parseTerm(String rawString) throws Exception {
		Scanner s = new Scanner(new StringReader(rawString));
		return parseTerm(s);		
	}
	
	
	/**
	 * Creates a HOL type from a raw string description
	 */
	public final static HOLType parseType(String rawString) throws Exception {
		Scanner s = new Scanner(new StringReader(rawString));
		return parseType(s);		
	}
	

	
	
	/**
	 * Parses a type variable
	 */
	protected static HOLType parseTyvar(Scanner s) throws Exception {
		// Tyvar
		Token t = s.nextToken();
		
		if (t.type != TokenType.Tyvar)
			throw new Exception("Tyvar expected: " + t);
		
		// (
		t = s.nextToken();
		if (t.type != TokenType.LPAR)
			throw new Exception("( expected: " + t);
		
		// name
		t = s.nextToken();
		if (t.type != TokenType.STRING)
			throw new Exception("STRING expected: " + t);
		
		HOLType result = HOLType.mk_vartype(t.value);
		
		// )
		t = s.nextToken();
		if (t.type != TokenType.RPAR)
			throw new Exception(") expected: " + t);
		
		return result;
	}
	
	
	/**
	 * Parses a HOL type application
	 */
	protected static HOLType parseTyapp(Scanner s) throws Exception {
		// Tyapp
		Token t = s.nextToken();
		
		if (t.type != TokenType.Tyapp)
			throw new Exception("Tyapp expected: " + t);
		
		// (
		t = s.nextToken();
		if (t.type != TokenType.LPAR)
			throw new Exception("( expected: " + t);
		
		// name
		t = s.nextToken();
		if (t.type != TokenType.STRING)
			throw new Exception("STRING expected: " + t);
		
		String name = t.value;
		ArrayList<HOLType> args = new ArrayList<HOLType>();
		
		// [
		t = s.nextToken();
		if (t.type != TokenType.LBRACK)
			throw new Exception("[ expected: " + t);
		
		t = s.peekToken();
		if (t.type == TokenType.RBRACK) {
			// ]
			s.nextToken();
		}
		else {
			while (true) {
				HOLType arg = parseType(s);
				args.add(arg);
				
				t = s.nextToken();
				if (t.type == TokenType.RBRACK)
					break;
				
				if (t.type != TokenType.COMMA)
					throw new Exception(", expected: " + t);
			}
		}
		
		// )
		t = s.nextToken();
		if (t.type != TokenType.RPAR)
			throw new Exception(") expected: " + t);
		
		return HOLType.mk_type(name, args);
	}
	
	
	/**
	 * Parses a variable term
	 */
	protected static Term parseVar(Scanner s) throws Exception {
		// Var
		Token t = s.nextToken();
		
		if (t.type != TokenType.Var)
			throw new Exception("Var expected: " + t);
		
		// (
		t = s.nextToken();
		if (t.type != TokenType.LPAR)
			throw new Exception("( expected: " + t);
		
		// name
		t = s.nextToken();
		if (t.type != TokenType.STRING)
			throw new Exception("STRING expected: " + t);
		
		String name = t.value;

		// ,
		t = s.nextToken();
		if (t.type != TokenType.COMMA)
			throw new Exception("COMMA expected: " + t);
		
		HOLType type = parseType(s);
		
		// )
		t = s.nextToken();
		if (t.type != TokenType.RPAR)
			throw new Exception(") expected: " + t);
		
		return Term.mk_var(name, type);
	}
	
	/**
	 * Parses a constant term
	 */
	protected static Term parseConst(Scanner s) throws Exception {
		// Const
		Token t = s.nextToken();
		
		if (t.type != TokenType.Const)
			throw new Exception("Const expected: " + t);
		
		// (
		t = s.nextToken();
		if (t.type != TokenType.LPAR)
			throw new Exception("( expected: " + t);
		
		// name
		t = s.nextToken();
		if (t.type != TokenType.STRING)
			throw new Exception("STRING expected: " + t);
		
		String name = t.value;

		// ,
		t = s.nextToken();
		if (t.type != TokenType.COMMA)
			throw new Exception("COMMA expected: " + t);
		
		HOLType type = parseType(s);
		
		// )
		t = s.nextToken();
		if (t.type != TokenType.RPAR)
			throw new Exception(") expected: " + t);
		
		return Term.mk_mconst(name, type);
	}
	

	/**
	 * Parses a combinator term
	 */
	protected static Term parseComb(Scanner s) throws Exception {
		// Comb
		Token t = s.nextToken();
		
		if (t.type != TokenType.Comb)
			throw new Exception("Comb expected: " + t);
		
		// (
		t = s.nextToken();
		if (t.type != TokenType.LPAR)
			throw new Exception("( expected: " + t);

		// f
		Term f = parseTerm(s);

		// ,
		t = s.nextToken();
		if (t.type != TokenType.COMMA)
			throw new Exception("COMMA expected: " + t);
		
		// a
		Term a = parseTerm(s);
		
		// )
		t = s.nextToken();
		if (t.type != TokenType.RPAR)
			throw new Exception(") expected: " + t);
		
		return Term.mk_comb(f, a);
	}
	
	
	/**
	 * Parses an abstraction term
	 */
	protected static Term parseAbs(Scanner s) throws Exception {
		// Abs
		Token t = s.nextToken();
		
		if (t.type != TokenType.Abs)
			throw new Exception("Abs expected: " + t);
		
		// (
		t = s.nextToken();
		if (t.type != TokenType.LPAR)
			throw new Exception("( expected: " + t);

		// v
		Term v = parseTerm(s);

		// ,
		t = s.nextToken();
		if (t.type != TokenType.COMMA)
			throw new Exception("COMMA expected: " + t);
		
		// b
		Term b = parseTerm(s);
		
		// )
		t = s.nextToken();
		if (t.type != TokenType.RPAR)
			throw new Exception(") expected: " + t);
		
		return Term.mk_abs(v, b);
	}
	
}
