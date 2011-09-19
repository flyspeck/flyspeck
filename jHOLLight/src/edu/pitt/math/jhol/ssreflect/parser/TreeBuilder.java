package edu.pitt.math.jhol.ssreflect.parser;

import java.util.ArrayList;

import edu.pitt.math.jhol.ssreflect.parser.tree.*;

/**
 * Builds a syntactic tree
 */
public class TreeBuilder {
	// The scanner
	private final Scanner scanner;

	/**
	 * Initializes a builder using the provided scanner
	 */
	public TreeBuilder(Scanner scanner) {
		assert(scanner != null);
		this.scanner = scanner;
	}
	
	/**
	 * Parses an expression in the "global" mode
	 * @return
	 * @throws Exception
	 */
	public Node parseGlobal() throws Exception {
		// Raw command
		String rawStr = tryParseRawExpr();
		if (rawStr != null)
			return new RawNode(rawStr);
		
		// Lemma
		Token t = scanner.peekToken();
		if (t.type != TokenType.IDENTIFIER)
			throw new Exception("IDENTIFIER expected: " + t);

		if (t.value == "Lemma")
			return parseLemma();
		
		if (t.value == "Section" || t.value == "End")
			return parseSection();
		
		if (t.value == "Variable" || t.value == "Variables")
			return parseVariables();
		
		if (t.value == "Hypothesis")
			return parseHypothesis();
		
		throw new Exception("Unknown command: " + t);
	}
	
	
	/**
	 * Parses a lemma description
	 */
	private LemmaNode parseLemma() throws Exception {
		// Lemma
		Token t = scanner.nextToken();
		if (t.type != TokenType.IDENTIFIER || t.value != "Lemma")
			throw new Exception("'Lemma' expected: " + t);
		
		// name
		t = scanner.nextToken();
		if (t.type != TokenType.IDENTIFIER)
			throw new Exception("Lemma name expected: " + t);
		
		String name = t.value;
		
		// :
		t = scanner.nextToken();
		if (t.type != TokenType.COLON)
			throw new Exception(": expected: " + t);
		
		// goal
		String raw = tryParseRawExpr();
		if (raw == null)
			throw new Exception("goal expected: " + t);
		
		RawObjectNode goal = new RawObjectNode(raw);
		return new LemmaNode(name, goal);
	}
	
	
	/**
	 * Parses section variables
	 */
	private SectionVariableNode parseVariables() throws Exception {
		// Lemma
		Token t = scanner.nextToken();
		if (t.type != TokenType.IDENTIFIER || (t.value != "Variable" && t.value != "Variables"))
			throw new Exception("'Variable' expected: " + t);
		
		// Names
		ArrayList<String> names = new ArrayList<String>();
		
		while (true) {
			t = scanner.peekToken();
			if (t.type != TokenType.IDENTIFIER)
				break;
			
			// Name
			scanner.nextToken();
			names.add(t.value);
		}
		
		if (names.size() == 0)
			throw new Exception("Name(s) expected: " + t);
		
		// :
		t = scanner.nextToken();
		if (t.type != TokenType.COLON)
			throw new Exception(": expected: " + t);
		
		// type
		String raw = tryParseRawExpr();
		if (raw == null)
			throw new Exception("type expected: " + t);
		
		RawObjectNode type = new RawObjectNode(raw);
		return new SectionVariableNode(names, type);
	}
	
	
	/**
	 * Parses a section hypothesis
	 */
	private SectionHypothesisNode parseHypothesis() throws Exception {
		// Lemma
		Token t = scanner.nextToken();
		if (t.type != TokenType.IDENTIFIER || t.value != "Hypothesis")
			throw new Exception("'Hypothesis' expected: " + t);
		
		// name
		t = scanner.nextToken();
		if (t.type != TokenType.IDENTIFIER)
			throw new Exception("Hypothesis name expected: " + t);
		
		String name = t.value;
		
		// :
		t = scanner.nextToken();
		if (t.type != TokenType.COLON)
			throw new Exception(": expected: " + t);
		
		// term
		ObjectNode term = tryParseObject();
		if (term == null)
			throw new Exception("OBJECT expected: " + t);
		
		return new SectionHypothesisNode(name, term);
	}
	
	
	/**
	 * Section "Name" or End "Name"
	 */
	private SectionNode parseSection() throws Exception {
		boolean startFlag = false;
		
		// Section or End
		Token t = scanner.nextToken();
		if (t.type != TokenType.IDENTIFIER)
			throw new Exception("Section or End expected: " + t);
		
		if (t.value == "Section")
			startFlag = true;
		else if (t.value == "End")
			startFlag = false;
		else
			throw new Exception("Section or End expected: " + t);
		
		// Name
		t = scanner.nextToken();
		if (t.type != TokenType.IDENTIFIER)
			throw new Exception("IDENTIFIER expected: " + t);

		return new SectionNode(startFlag, t.value);
	}
	
	
	/**
	 * Parses an expression in the "proof" mode
	 */
	public TacticNode parseProof() throws Exception {
		TacticChainNode chain = new TacticChainNode();
		
		while (true) {
			TacticNode tactic = parseProofExpression();
			chain.add(tactic);
			
			Token t = scanner.peekToken();
			if (t.type == TokenType.SEMICOLON) {
				// ;
				scanner.nextToken();
			}
			else {
				if (t.type != TokenType.PERIOD)
					throw new Exception(". expected: " + t);
				// Do not consume . here
				break;
			}
		}
		
		return chain;
	}
	
	/**
	 * Parses a proof expression in the form
	 * tactic[: intro][=> disch]
	 */
	private TacticNode parseProofExpression() throws Exception {
		TacticChainNode chain = new TacticChainNode();
		
		TacticNode tactic = parseFirstTactic();
		TacticNode disch = null;
		TacticNode intro = null;

		// : or =>
		Token t = scanner.peekToken();
		if (t.type == TokenType.COLON) {
			// :
			scanner.nextToken();
			intro = parseIntro();
		}

		// =>
		t = scanner.peekToken();
		if (t.type == TokenType.ARROW) {
			// =>
			scanner.nextToken();
			disch = tryParseDisch();
			if (disch == null)
				throw new Exception("null disch: " + t);
		}
		
		chain.add(intro);
		chain.add(tactic);
		chain.add(disch);
		
		if (chain.isEmpty())
			throw new Exception("Empty tactic");
		
		return chain;
	}
	
	
	/**
	 * Parses the introduction expressions
	 */
	private TacticNode parseIntro() throws Exception {
		TacticChainNode chain = new TacticChainNode();
		
		while (true) {
			ObjectNode obj = tryParseObject();
			if (obj == null)
				break;
			
			chain.add(new IntroNode(obj));
		}
		
		if (chain.isEmpty())
			throw new Exception("empty intro: " + scanner.peekToken());
		
		return chain;
	}
	
	
	/**
	 * Parses the discharge expressions
	 * Returns null if nothing can be parsed
	 */
	private TacticNode tryParseDisch() throws Exception {
		TacticChainNode chain = new TacticChainNode();
		
		while (true) {
			TacticNode simp = tryParseSimp();
			chain.add(simp);

			ObjectNode obj = null;
			
			Token t = scanner.peekToken();
			if (t.type == TokenType.LBRACK) {
				// []-pattern
				TacticNode tac = parseDischCasePattern();
				chain.add(tac);
				continue;
			}
			
			if (t.type == TokenType.UNDERSCORE) {
				// _
				scanner.nextToken();
				obj = new WildObjectNode();
			}
			else if (t.type == TokenType.IDENTIFIER) {
				// Id
				scanner.nextToken();
				obj = new IdNode(t.value);
			}
			
			if (obj == null)
				break;
			
			DischNode disch = new DischNode(obj);
			chain.add(disch);
		}
		
		if (chain.isEmpty())
			return null;
		
		return chain;
	}
	
	
	/**
	 * Parses expression of the form move => [a b [c d]]
	 * @return
	 */
	private TacticNode parseDischCasePattern() throws Exception {
		TacticChainNode chain = new TacticChainNode();
		Token t = scanner.nextToken();
		if (t.type != TokenType.LBRACK)
			throw new Exception("[ expected: " + t);
		
		// Immediately add one case command
		chain.add(new CaseElimNode(false));
		
		ArrayList<TacticNode> tactics = new ArrayList<TacticNode>();
		
		while (true) {
			// Parse Id's and other []-patterns only
			// Id or [ or ]
			t = scanner.peekToken();
			
			if (t.type == TokenType.RBRACK) {
				// ]
				scanner.nextToken();
				break;
			}
			
			if (t.type == TokenType.LBRACK) {
				// [
				TacticNode tac = parseDischCasePattern();
				tactics.add(tac);
				continue;
			}
			
			if (t.type != TokenType.IDENTIFIER)
				throw new Exception("IDENTIFIER or ] expected: " + t);
			
			// Id
			scanner.nextToken();
			
			IdNode id = new IdNode(t.value);
			DischNode disch = new DischNode(id);
			tactics.add(disch);
		}
		
		int n = tactics.size();
		for (int i = 0; i < n; i++) {
			chain.add(tactics.get(i));
			if (i < n - 2)
				chain.add(new CaseElimNode(false));
		}
		
		return chain;
	}
	
	
	/**
	 * Parses simplification expressions
	 * Returns null if nothing can be parsed
	 */
	private TacticNode tryParseSimp() throws Exception {
		Token t = scanner.peekToken();
		
		// Simp
		if (t.type == TokenType.SIMP) {
			// /=
			scanner.nextToken();
			return new RawTactic("SIMP_TAC[]");
		}
		
		// TrivSimp
		if (t.type == TokenType.TRIV_SIMP) {
			// //=
			scanner.nextToken();
			return new RawTactic("ASM_SIMP_TAC[]");
		}
		
		// Triv
		if (t.type == TokenType.TRIV) {
			// //
			scanner.nextToken();
			return new RawTactic("ASM_REWRITE_TAC[]");
		}

		return null;
	}
	
	
	/*
	 * Parses a raw expression in the form "..." or "`...`"
	 * Returns null if nothing is parsed
	 */
	public String tryParseRawExpr() throws Exception {
/*		// ` or {
		Token t = scanner.peekToken();
		boolean termFlag = false;
		
		if (t.type == TokenType.BACK_QUOTE)
			termFlag = true;
		else if (t.type != TokenType.LBRACE)
			return null;
		
		// ` or {
		t = scanner.nextToken();
		scanner.yybegin(Scanner.RAW);
		scanner.string.setLength(0);
		// string + ` or }
		t = scanner.nextToken();
		
		if (t.type != TokenType.STRING)
			throw new Exception("STRING expected: " + t);
		
		String str = t.value;
		if (termFlag)
			str = "`" + str + "`";
		
		return str;
*/
		
		Token t = scanner.peekToken();
		if (t.type == TokenType.STRING) {
			// STRING
			scanner.nextToken();
			return t.value;
		}
		
		return null;
		
	}
	
	
	/**
	 * Parses a tactics
	 */
	private TacticNode parseFirstTactic() throws Exception {
		TacticNode tactic = null;
		TacticNode view = null;
		Token t;
		
		// Try to get a raw expression
		String raw = tryParseRawExpr();	
		if (raw != null) {
			tactic = new RawTactic(raw);
		}
		else {
			t = scanner.nextToken();
			if (t.type != TokenType.IDENTIFIER)
				throw new Exception("IDENTIFIER expected: " + t);
			
			// move
			if (t.value == "move")
				tactic = null;
			// case
			else if (t.value == "case")
				tactic = new CaseElimNode(false);
			// elim
			else if (t.value == "elim")
				tactic = new CaseElimNode(true);
			// apply
			else if (t.value == "apply")
				tactic = new ApplyNode();
			// rewrite
			else if (t.value == "rewrite")
				tactic = parseRewriteBody(false);
			// rewr: "native" HOL Light rewriting
			else if (t.value == "rewr")
				tactic = parseRewriteBody(true);
			// have
			else if (t.value == "have")
				tactic = parseHaveBody();
			// set
			else if (t.value == "set")
				tactic = parseSetBody();
			// exists
			else if (t.value == "exists")
				tactic = parseExistsBody();
			// left
			else if (t.value == "left")
				tactic = new RawTactic("DISJ1_TAC");
			// right
			else if (t.value == "right")
				tactic = new RawTactic("DISJ2_TAC");
			// split
			else if (t.value == "split")
				tactic = new RawTactic("CONJ_TAC");
			else
				throw new Exception("Unknown tactic: " + t);
		}
		
		// View
		t = scanner.peekToken();
		if (t.type == TokenType.SLASH) {
			// /
			scanner.nextToken();
			view = parseViewBody();
		}

		if (tactic == null && view == null)
			return null;
		
		TacticChainNode chain = new TacticChainNode();
		chain.add(view);
		chain.add(tactic);
		
		return chain;
	}
	
	
	/**
	 * View body: /X or /(_ X)
	 */
	private TacticNode parseViewBody() throws Exception {
		ObjectNode obj = tryParseObject();
		if (obj == null)
			throw new Exception("OBJECT expected: " + scanner.peekToken());
		
		ViewNode view = new ViewNode(obj);
		return view;
	}
	
	
	/**
	 * Parses the body of an "exists" expression
	 */
	private TacticNode parseExistsBody() throws Exception {
		TacticChainNode chain = new TacticChainNode();
		
		while (true) {
			ObjectNode obj = tryParseObject();
			if (obj == null)
				break;
			
			ExistsNode exists = new ExistsNode(obj);
			chain.add(exists);
		}
		
		if (chain.isEmpty())
			throw new Exception("empty exists: " + scanner.peekToken());
		
		return chain;
	}
	

	/**
	 * Parses the body of a "set" expression
	 */
	private TacticNode parseSetBody() throws Exception {
		// Id
		Token t = scanner.nextToken();
		if (t.type != TokenType.IDENTIFIER)
			throw new Exception("IDENTIFIER expected: " + t);
		
		IdNode id = new IdNode(t.value);
		
		// :=
		t = scanner.nextToken();
		if (t.type != TokenType.ASSIGN)
			throw new Exception(":= expected: " + t);
		
		// term
		ObjectNode obj = tryParseObject();
		if (obj == null)
			throw new Exception("OBJECT expected: " + t);
		
		SetNode set = new SetNode(id, obj);
		return set;
	}
	
	
	/**
	 * Parses the body of a "have" expression
	 */
	private TacticNode parseHaveBody() throws Exception {
		TacticNode disch = tryParseDisch();

		boolean assignFlag;
		
		// : or :=
		Token t = scanner.nextToken();
		if (t.type == TokenType.ASSIGN) {
			assignFlag = true;
		}
		else if (t.type == TokenType.COLON) {
			assignFlag = false;
		}
		else  {
			throw new Exception(": or := expected: " + t);
		}
		
		ObjectNode obj = null;
		
		if (assignFlag) {
			obj = parseApplicationBody();
		}
		else {
			obj = tryParseObject();
		}
		
		if (obj == null)
			throw new Exception("OBJECT expected: " + t);
		
		HaveNode have = new HaveNode(disch, obj, assignFlag);
		return have;
	} 
	
	
	/**
	 * Parses the body of a "rewrite" expression
	 */
	private TacticNode parseRewriteBody(boolean useHolRewrite) throws Exception {
		TacticChainNode chain = new TacticChainNode();
		
		while (true) {
			boolean revFlag = false;
			boolean exactFlag = true;
			boolean repeatFlag = false;
			int rewrites = -1;
			
			TacticNode simp = tryParseSimp();
			chain.add(simp);
			
			Token t = scanner.peekToken();
			// RevFlag
			if (t.type == TokenType.DASH) {
				// -
				scanner.nextToken();
				revFlag = true;
			}
			
			// Number of rewrites
			t = scanner.peekToken();
			if (t.type == TokenType.INTEGER) {
				// number
				scanner.nextToken();
				rewrites = t.intValue;

				// -3 <=> - 3
				if (rewrites < 0) {
					revFlag = true;
					rewrites = -rewrites;
				}
					
				if (rewrites < 1)
					throw new Exception("The number of rewrites should be >= 1: " + t);
				
				t = scanner.peekToken();
				if (t.type != TokenType.EXCLAMATION && t.type != TokenType.QUESTION)
					throw new Exception("! or ? expected: " + t);
			}
			
			// ! or ?
			t = scanner.peekToken();
			if (t.type == TokenType.EXCLAMATION || t.type == TokenType.QUESTION) {
				// ! or ?
				scanner.nextToken();
				exactFlag = (t.type == TokenType.EXCLAMATION);
				if (rewrites <= 0)
					repeatFlag = true;
			}
			
			if (rewrites <= 0)
				rewrites = 1;
				
			// Theorem
			ObjectNode thm = tryParseObject();
			if (thm == null) {
				if (revFlag)
					throw new Exception("THEOREM expected: " + t);
				break;
			}
			
			RewriteNode r = new RewriteNode(thm, useHolRewrite, revFlag, rewrites, repeatFlag, exactFlag);
			chain.add(r);
		}
		
		if (chain.isEmpty())
			throw new Exception("empty rewrite: " + scanner.peekToken());
		
		return chain;
	}
	
	
	/**
	 * Parses an object (theorem, term, application)
	 */
	private ObjectNode tryParseObject() throws Exception {
		// Raw expression
		String raw = tryParseRawExpr();
		if (raw != null) {
			return new RawObjectNode(raw);
		}
		
		Token t = scanner.peekToken();
		boolean getTypeFlag = false;
		ObjectNode obj = null;
		
		if (t.type == TokenType.AT) {
			// @: get type
			scanner.nextToken();
			getTypeFlag = true;
		}

		t = scanner.peekToken();
		
		if (t.type == TokenType.LPAR) {
			// Application
			// (
			scanner.nextToken();
			obj = parseApplicationBody();
			// )
			t = scanner.nextToken();
			if (t.type != TokenType.RPAR)
				throw new Exception(") expected: " + t);
		}
		else if (t.type == TokenType.UNDERSCORE) {
			// _
			scanner.nextToken();
			obj = new WildObjectNode();
		}
		else if (t.type == TokenType.IDENTIFIER) {
			// Id
			scanner.nextToken();
			obj = new IdNode(t.value);
		}

		if (obj == null) {
			if (!getTypeFlag)
				return null;
			throw new Exception("Object expected after @: " + t);
		}
		
		if (!getTypeFlag)
			return obj;
		
		return new GetTypeNode(obj);
	}

	
	/**
	 * Parses an application body
	 */
	private ApplicationNode parseApplicationBody() throws Exception {
		ArrayList<ObjectNode> objs = new ArrayList<ObjectNode>();
		
		// Read in all objects
		while (true) {
			ObjectNode obj = tryParseObject();
			if (obj == null) {
				break;
			}
			
			objs.add(obj);
		}
		
		if (objs.size() == 0)
			throw new Exception("null application: " + scanner.peekToken());
		
		// Create an application node
		ObjectNode first = objs.remove(0);
		ObjectNode arg = null;
		if (objs.size() > 0) {
			arg = objs.remove(0);
		}
		
		ApplicationNode app = new ApplicationNode(first, arg);

		for (int i = 0; i < objs.size(); i++) {
			arg = objs.get(i);
			app = new ApplicationNode(app, arg);
		}
		
		return app;
	}

}
