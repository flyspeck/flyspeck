package edu.pitt.math.jhol.ssreflect.parser;

import java.util.ArrayList;

import edu.pitt.math.jhol.ssreflect.parser.tree.*;
import edu.pitt.math.jhol.ssreflect.parser.tree.RewriteNode.RewriteParameters;

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
		
		if (t.value == "Variable" || t.value == "Variables" || t.value == "Implicit")
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
		
		// name and parameters
		ArrayList<String> ids = parseIdList();
		if (ids.size() == 0)
			throw new Exception("Lemma name expected: " + t);
		
		String name = ids.get(0);
		String[] params = new String[ids.size() - 1];
		for (int i = 0; i < params.length; i++)
			params[i] = ids.get(i + 1);
		
		// :
		t = scanner.nextToken();
		if (t.type != TokenType.COLON)
			throw new Exception(": expected: " + t);
		
		// goal
		String raw = tryParseRawExpr();
		if (raw == null)
			throw new Exception("goal expected: " + t);
		
		RawObjectNode goal = new RawObjectNode(raw);
		return new LemmaNode(name, params, goal);
	}
	
	
	/**
	 * Parses a list of identifiers and returns their names (the result could be empty)
	 */
	private ArrayList<String> parseIdList() throws Exception {
		ArrayList<String> ids = new ArrayList<String>();
		
		while (true) {
			Token t = scanner.peekToken();
			if (t.type != TokenType.IDENTIFIER)
				break;
			
			// id
			scanner.nextToken();
			ids.add(t.value);
		}
		
		return ids;
	}
	
	
	/**
	 * Parses section variables
	 */
	private SectionVariableNode parseVariables() throws Exception {
		boolean implicitType = false;
		
		// Variable or Implicit
		Token t = scanner.nextToken();
		if (t.type != TokenType.IDENTIFIER || 
				(t.value != "Variable" && t.value != "Variables" && t.value != "Implicit"))
			throw new Exception("'Variable or Implicit Type' expected: " + t);
		
		// Implicit [Type] or Implicit [Types] 
		if (t.value == "Implicit") {
			t = scanner.peekToken();
			if (t.type == TokenType.IDENTIFIER && (t.value == "Type" || t.value == "Types"))
				// Type or Types
				scanner.nextToken();
			
			implicitType = true;
		}
		
		
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
		return new SectionVariableNode(names, type, implicitType);
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
		Token t = scanner.peekToken();
		if (t.type == TokenType.IDENTIFIER && t.value == "Proof") {
			// Silently ignore the Proof command
			scanner.nextToken();
			// Should be .
			t = scanner.nextToken();
			if (t.type != TokenType.PERIOD)
				throw new Exception(". expected: " + t);
		}
		
		TacticChainNode chain = parseTacticChain();
		
		// . (do not consume it here)		
		t = scanner.peekToken();
		if (t.type != TokenType.PERIOD)
			throw new Exception(". expected: " + t);
		
		return chain;
	}
	
	
	/**
	 * Parses an expression of the form
	 * tactic; tactic; by tactic
	 */
	private TacticChainNode parseTacticChain() throws Exception {
		TacticChainNode chain = new TacticChainNode();
		
		while (true) {
			boolean processedFlag = false;
			Token t = scanner.peekToken();
		
			// [tac1 | ... ]
			if (t.type == TokenType.LBRACK) {
				chain.add(parseParallelTactics());
				processedFlag = true;
			}
			// first, last
			else if (t.type == TokenType.IDENTIFIER) {
				// first or last
				if (t.value == "first" || t.value == "last") {
					boolean firstFlag = t.value == "first";
					int rot = 1;
					// first or last
					scanner.nextToken();
					
					t = scanner.peekToken();
					if (t.type == TokenType.INTEGER ||
							(t.type == TokenType.IDENTIFIER && (t.value == "last" || t.value == "first"))) {
						// integer, last, first
						scanner.nextToken();
						
						// first [n] last or last [n] first
						if (t.type == TokenType.INTEGER) {
							rot = t.intValue;
							// Should be last or first
							t = scanner.nextToken();
						}

						if (t.type != TokenType.IDENTIFIER)
							throw new Exception("'last' or 'first' expected: " + t);

						TacticNode rot_tac;
						
						if (firstFlag) {
							if (t.value != "last")
								throw new Exception("'last' expected: " + t);
							rot_tac = new RawTactic("THENL_ROT (" + rot + ')');
						}
						else {
							if (t.value != "first")
								throw new Exception("'first' expected: " + t);
							rot_tac = new RawTactic("THENL_ROT (" + (-rot) + ')');
						}
						
						TacticNode left = chain;
						chain = new TacticChainNode();
						
						chain.add(new BinaryNode(rot_tac, left, null));
						processedFlag = true;
					}
					else {
						if (chain.isEmpty())
							throw new Exception("first, last: empty left hand side " + t);
						
						TacticNode right = parseProofExpression();
						TacticNode left = chain;
						chain = new TacticChainNode();
						
						TacticNode tac = new RawTactic(firstFlag ? "THENL_FIRST" : "THENL_LAST");
						BinaryNode bin = new BinaryNode(tac, left, right);
						chain.add(bin);
						
						processedFlag = true;
					}
				}
			}

			// tactic
			if (!processedFlag) {
				TacticNode tac = parseProofExpression();
				chain.add(tac);
			}
			
			// semicolon
			t = scanner.peekToken();
			if (t.type == TokenType.SEMICOLON) {
				// ;
				scanner.nextToken();
				continue;
			}
			
			break;
		}
		
		return chain;
	}
	
	
	/**
	 * Parses expressions of the form [tac1 | tac2 | ... ]
	 * @return
	 * @throws Exception
	 */
	private TacticParallelNode parseParallelTactics() throws Exception {
		TacticParallelNode ts = new TacticParallelNode();
		
		Token t = scanner.nextToken();
		if (t.type != TokenType.LBRACK)
			throw new Exception("[ expected: " + t);
		
		// Parse all tactics
		while (true) {
			TacticChainNode chain = parseTacticChain();
			ts.add(chain);
		
			// ] or |
			t = scanner.nextToken();
			if (t.type == TokenType.RBRACK)
				break;
			
			if (t.type != TokenType.BAR)
				throw new Exception("] or | expected: " + t);
		}
		
		return ts;
	}
	
	
	/**
	 * Parses a proof expression in the form
	 * tactic[: intro][=> disch]
	 */
	private TacticNode parseProofExpression() throws Exception {
		TacticChainNode chain = new TacticChainNode();

		Token t = scanner.peekToken();
		// by
		if (t.value == "by") {
			// by
			scanner.nextToken();
			chain = parseTacticChain();
			chain.add(new RawTactic("done_tac"));
			return chain;
		}
		
		TacticChainNode tactic = parseFirstTactic();
		TacticNode disch = null;
		TacticNode intro = null;

		// : or =>
		t = scanner.peekToken();
		if (t.type == TokenType.COLON) {
			// :
			scanner.nextToken();
			intro = parseDisch();
		}

		// =>
		t = scanner.peekToken();
		if (t.type == TokenType.ARROW) {
			// =>
			scanner.nextToken();
			
			// Indicates if the first [] is a destructive pattern
			boolean firstDestructive = false;
			if (tactic.size() > 0 && tactic.get(tactic.size() - 1) instanceof MoveNode) {
				firstDestructive = true;
			}
			
			disch = tryParseIntro(firstDestructive);
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
	 * Parses discharging expressions
	 */
	private TacticNode parseDisch() throws Exception {
		TacticChainNode chain = new TacticChainNode();
		ArrayList<DischNode> dischs = new ArrayList<DischNode>();
		
		while (true) {
			ObjectNode obj = tryParseObject();
			if (obj == null)
				break;
		
			dischs.add(new DischNode(obj));
		}
		
		int n = dischs.size();
		if (n == 0)
			throw new Exception("empty disch: " + scanner.peekToken());
		
		// Revert the order of discharges
		for (int i = n - 1; i >= 0; i--) {
			chain.add(dischs.get(i));
		}
		
		return chain;
	}
	
	
	/**
	 * Parses introduction expressions
	 * Returns null if nothing can be parsed
	 */
	private TacticNode tryParseIntro(boolean firstDestructive) throws Exception {
		TacticChainNode chain = new TacticChainNode();
		boolean destructiveFlag = firstDestructive;
		Token t;
		
		while (true) {
			TacticNode simp = tryParseSimp();
			chain.add(simp);

			ObjectNode obj = null;
			// TODO: parsing of rewrite parameters requires look ahead operations
//			RewriteParameters params = tryParseRewriteParameters();
			RewriteParameters params = new RewriteParameters();
			t = scanner.peekToken();
			
			boolean arrowFlag = t.type == TokenType.LEFT_ARROW || t.type == TokenType.RIGHT_ARROW;
			
			if (params.modifiedFlag && !arrowFlag)
				throw new Exception("<- or -> expected: " + t);

			// <- or ->
			if (arrowFlag) {
				// <- or ->
				scanner.nextToken();
				params.revFlag = t.type == TokenType.LEFT_ARROW;
				TacticNode rewrite = new RewriteNode(params, IdNode.TMP_ID, true, false);
				chain.add(rewrite);
				continue;
			}
			
			if (t.type == TokenType.LBRACK) {
				// []-pattern
				TacticNode tac = parseIntroCasePattern(destructiveFlag);
				chain.add(tac);
				destructiveFlag = true;
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
			
			IntroductionNode disch = new IntroductionNode(obj);
			chain.add(disch);
		}
		
		if (chain.isEmpty())
			return null;
		
		return chain;
	}
	
	
	/**
	 * Parses expression of the form move => [a b [c | d]]
	 * @return
	 */
	private TacticNode parseIntroCasePattern(boolean destructiveFlag) throws Exception {
		TacticChainNode result = new TacticChainNode();
		TacticParallelNode chains = new TacticParallelNode();
		TacticChainNode chain = new TacticChainNode();
		
		if (destructiveFlag)
			result.add(new CaseElimNode(false));
		
		Token t = scanner.nextToken();
		if (t.type != TokenType.LBRACK)
			throw new Exception("[ expected: " + t);
		
		while (true) {
			TacticNode tactic = tryParseIntro(true);
			chain.add(tactic);

			// ] or |
			t = scanner.nextToken();
			
			// ]
			if (t.type == TokenType.RBRACK) {
				break;
			}
			
			// |
			if (t.type == TokenType.BAR) {
				chains.add(chain);
				chain = new TacticChainNode();
				continue;
			}
			
			throw new Exception("| or ] expected: " + t);
		}

		if (chains.size() == 0) {
			result.add(chain);
		}
		else {
			chains.add(chain);
			result.add(chains);
		}
		
		return result;
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
			return new RawTactic("simp_tac");
		}
		
		// TrivSimp
		if (t.type == TokenType.TRIV_SIMP) {
			// //=
			scanner.nextToken();
			return new RawTactic("(simp_tac THEN TRY done_tac)"); 
		}
		
		// Triv
		if (t.type == TokenType.TRIV) {
			// //
			scanner.nextToken();
			return new RawTactic("(TRY done_tac)");
		}

		return null;
	}
	
	
	/*
	 * Parses a raw expression in the form "..." or "`...`"
	 * Returns null if nothing is parsed
	 */
	public String tryParseRawExpr() throws Exception {
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
	private TacticChainNode parseFirstTactic() throws Exception {
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

			// do
			if (t.value == "do")
				tactic = parseDoBody();
			// exact
			else if (t.value == "exact")
				tactic = new RawTactic("exact_tac");
			// done
			else if (t.value == "done")
				tactic = new RawTactic("done_tac");
			// arith
			else if (t.value == "arith")
				tactic = new RawTactic("arith_tac");
			// move
			else if (t.value == "move")
				tactic = new MoveNode();
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
				tactic = parseHaveBody(false);
			else if (t.value == "suff")
				tactic = parseHaveBody(true);
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
				tactic = new RawTactic("split_tac");
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
	private TacticNode parseHaveBody(boolean suffFlag) throws Exception {
		TacticNode disch = tryParseIntro(false);

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
		if (suffFlag) {
			TacticNode rot_tac = new RawTactic("(THENL_ROT 1)");
			BinaryNode bin = new BinaryNode(rot_tac, have, null);
			return bin;
		}
		
		return have;
	}
	
	
	/**
	 * Parses the occ-switch: {1 2 -3}
	 * @return null if nothing can be parsed
	 */
	private ArrayList<Integer> tryParseOccSwitch() throws Exception {
		ArrayList<Integer> result = new ArrayList<Integer>();
		Token t = scanner.peekToken();
		if (t.type != TokenType.LBRACE)
			return null;

		// {
		scanner.nextToken();
		
		while (true) {
			// } or an integer
			t = scanner.nextToken();
			if (t.type == TokenType.RBRACE)
				break;
			
			if (t.type != TokenType.INTEGER)
				throw new Exception("} or an integer expected: " + t);
			
			result.add(t.intValue);
		}
		
		return result;
	}
	
	
	/**
	 * Parses a pattern expression [term]
	 * @return null if nothing can be parsed
	 */
	private ObjectNode tryParsePattern() throws Exception {
		Token t = scanner.peekToken();
		if (t.type != TokenType.LBRACK)
			return null;
		
		// [
		scanner.nextToken();
		
		ObjectNode obj = tryParseObject();
		if (obj == null)
			throw new Exception("Pattern expected: " + scanner.peekToken());
		
		// ]
		t = scanner.nextToken();
		if (t.type != TokenType.RBRACK)
			throw new Exception("] expected: " + t);
		
		return obj;
	}
	
	
	/**
	 * Parses the parameters of a rewrite operation
	 * @return default parameters if nothing can be parsed
	 */
	private RewriteNode.RewriteParameters tryParseRewriteParameters() throws Exception {
		RewriteNode.RewriteParameters params = new RewriteNode.RewriteParameters();
		params.rewrites = -1;
		
		Token t = scanner.peekToken();
		// RevFlag
		if (t.type == TokenType.DASH) {
			// -
			scanner.nextToken();
			params.modifiedFlag = true;
			params.revFlag = true;
		}

		// Number of rewrites
		t = scanner.peekToken();
		if (t.type == TokenType.INTEGER) {
			// number
			scanner.nextToken();
			params.modifiedFlag = true;
			params.rewrites = t.intValue;

			// -3 <=> - 3
			if (params.rewrites < 0) {
				params.revFlag = true;
				params.rewrites = -params.rewrites;
			}
				
			if (params.rewrites < 1)
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
			params.modifiedFlag = true;
			params.exactFlag = (t.type == TokenType.EXCLAMATION);
			if (params.rewrites <= 0)
				params.repeatFlag = true;
		}

		if (params.rewrites <= 0)
			params.rewrites = 1;
		
		// occ-switch {...}
		params.occ = tryParseOccSwitch();
		if (params.occ != null)
			params.modifiedFlag = true;
		
		// pattern [...]
		params.pattern = tryParsePattern();
		if (params.pattern != null)
			params.modifiedFlag = true;
		
		return params;
	}
	
	
	/**
	 * Parses a 'do'-expression
	 */
	private RepeatNode parseDoBody() throws Exception {
		int iterations = -1;
		boolean exactFlag = true;
		boolean repeatFlag = false;
		
		// Number of rewrites
		Token t = scanner.peekToken();
		if (t.type == TokenType.INTEGER) {
			// number
			scanner.nextToken();
			iterations = t.intValue;
			
			if (iterations < 0)
				throw new Exception("The number of iterations should be >= 0: " + t);
		}
		
		// ! or ?
		t = scanner.peekToken();
		if (t.type == TokenType.EXCLAMATION || t.type == TokenType.QUESTION) {
			// ! or ?
			scanner.nextToken();
			exactFlag = (t.type == TokenType.EXCLAMATION);
			if (iterations <= 0)
				repeatFlag = true;
		}

		if (iterations <= 0)
			iterations = 1;

		// Parse a tactic
		TacticParallelNode ts; 
		
		t = scanner.peekToken();
		if (t.type == TokenType.LBRACK) {
			ts = parseParallelTactics();
		}
		else {
			TacticNode tac = parseProofExpression();
			ts = new TacticParallelNode(tac);
		}
		
		return new RepeatNode(ts, iterations, repeatFlag, exactFlag);
	}
	
	
	/**
	 * Parses the body of a "rewrite" expression
	 */
	private TacticNode parseRewriteBody(boolean useHolRewrite) throws Exception {
		TacticChainNode chain = new TacticChainNode();
		
		while (true) {
			TacticNode simp = tryParseSimp();
			chain.add(simp);

			RewriteNode.RewriteParameters params = tryParseRewriteParameters();

			// Theorem
			ObjectNode thm = tryParseObject();
			if (thm == null) {
				if (params.modifiedFlag)
					throw new Exception("THEOREM expected: " + scanner.peekToken());
				break;
			}
			
			RewriteNode r = new RewriteNode(params, thm, false, useHolRewrite);
			RepeatNode repeat = new RepeatNode(r, params);
			chain.add(repeat);
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
