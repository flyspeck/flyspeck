package edu.pitt.math.jhol.ssreflect.parser;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.Stack;

import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.Goalstate;
import edu.pitt.math.jhol.ssreflect.parser.tree.GoalContext;
import edu.pitt.math.jhol.ssreflect.parser.tree.LemmaNode;
import edu.pitt.math.jhol.ssreflect.parser.tree.TacticNode;

/**
 * Converts the Coq-Ssreflect like text into HOL Light commands
 */
public class Interpreter {
	// Describes the last error
	private Exception error;
	
	// A Caml environment
	private CamlEnvironment caml;
	// The latest goal state
	private Goalstate state;
	// The scanner
	private Scanner scanner;
	
	// The base offset of the current script text
	private int baseTextPosition;
	
	// The active mode
	private int mode;
	// The name of the active lemma
	private String currentLemma;
	
	// Mode constants
	private final static int PROOF_MODE = 1;
	private final static int LEMMA_MODE = 2;
	
	// Information about all executed commands
	private final Stack<LemmaCommand> lemmaCommands;
	private final Stack<ProofCommand> proofCommands;

	// Listen for goal state updates
	private ArrayList<GoalListener> goalListeners = new ArrayList<GoalListener>();
	
	/**
	 * Listens for goal state updates
	 */
	public interface GoalListener {
		public void updateGoal(Goalstate state);
	}
	
	// Describes a command
	private abstract class CommandInfo {
		// The position of the last character of the command in the script text
		int endTextPosition;
		
		// Reverts the command
		// Returns true on success
		abstract boolean revert(); 
	}
	
	// A command in the "lemma" mode
	private class LemmaCommand extends CommandInfo {
		// If true, then the proof of the lemma has been completed
		boolean completeFlag;
		
		LemmaCommand(String lemmaName) {
			completeFlag = false;
		}
		
		boolean revert() {
			// TODO: undefine the lemma object 
			return true;
		}
	}
	
	// A command in the "proof" mode
	private class ProofCommand extends CommandInfo {
		public ProofCommand() {
		}
		
		public boolean revert() {
			try {
				caml.runCommand("b();;");
			}
			catch (Exception e) {
				e.printStackTrace();
				return false;
			}
			
			return true;
		}
	}
	
	/**
	 * Default constructor
	 */
	public Interpreter(CamlEnvironment caml) {
		assert(caml != null);
		this.caml = caml;
		this.mode = LEMMA_MODE;
		this.state = null;
		
		this.lemmaCommands = new Stack<LemmaCommand>();
		this.proofCommands = new Stack<ProofCommand>();
	}
	
	
	/**
	 * Adds a listener for goal updates
	 */
	public void addGoalListener(GoalListener listener) {
		if (goalListeners.contains(listener))
			return;
		
		goalListeners.add(listener);
	}
	
	
	/**
	 * Removes the given listener
	 */
	public void removeGoalListener(GoalListener listener) {
		goalListeners.remove(listener);
	}
	
	
	/**
	 * Returns errors of the last interpretation
	 */
	public Exception getError() {
		return error;
	}
	
	
	/**
	 * Returns the latest goal state
	 */
	public Goalstate getGoalstate() {
		return state;
	}
	
	
	/**
	 * Returns the active goal context
	 */
	private GoalContext getContext() throws Exception {
		if (state == null || state.numberOfGoals() == 0)
			throw new Exception("Empty goal");
		
		GoalContext context = new GoalContext(state.getGoal(0));
		return context;
	}
	
	
	/**
	 * Updates the goal state
	 * @throws Exception
	 */
	private void updateState(Goalstate newState) {
		if (newState.equals(state))
			return;
		
		state = newState;
		
		for (GoalListener listener : goalListeners) {
			listener.updateGoal(state);
		}
	}
	
	
	/**
	 * Updates the goal state
	 * @throws Exception
	 */
	private void getAndUpdateState() {
		try {
			Goalstate newState = (Goalstate) caml.execute("(hd o p)()", CamlType.GOAL_STATE);
			updateState(newState);
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	
	/**
	 * Runs the given command.
	 * The command will be not executed if there is no '.' after the command
	 * in the text.
	 */
	private void runCommand(String rawCmd) throws Exception {
		// .
		Token t = scanner.nextToken();
		if (t.type != TokenType.PERIOD)
			throw new Exception(". expected: " + t);
		
		// Run the command
		Goalstate newState = (Goalstate) caml.execute(rawCmd, CamlType.GOAL_STATE);
		updateState(newState);
		
		// Save the command in one of two stacks
		CommandInfo cmd = null;
		
		switch (mode) {
		// Proof
		case PROOF_MODE:
			cmd = proofCommands.push(new ProofCommand());
			break;
			
		// Lemma
		case LEMMA_MODE:
			cmd = lemmaCommands.push(new LemmaCommand(currentLemma));
			break;
		}
		
		// +1 for the period
		cmd.endTextPosition = baseTextPosition + t.ch + 1;
	}
	
	
	/**
	 * Returns the last command saved in the stack
	 */
	private CommandInfo getLastCommand() {
		if (proofCommands.size() > 0)
			return proofCommands.peek();

		if (lemmaCommands.size() > 0)
			return lemmaCommands.peek();
		
		return null;
	}
	
	
	/**
	 * Sets up the base text position using the information about
	 * executed commands
	 */
	private void setBaseTextPosition() {
		CommandInfo lastCmd = getLastCommand();
		
		if (lastCmd == null) {
			baseTextPosition = 0;
			return;
		}
		
		baseTextPosition = lastCmd.endTextPosition;
	}
	

	/**
	 * Interprets commands in the "proof" mode
	 */
	private void processProofMode(TreeBuilder builder) throws Exception {
		TacticNode node = builder.parseProof();
		
		// Qed or Abort?
		if (builder.getSwitchModeFlag()) {
			// Remove all proof commands and modify the previois lemma command
			proofCommands.clear();
			if (lemmaCommands.size() == 0)
				throw new Exception("No lemma corresponding to the proof");
			
			// Should be .
			Token t = scanner.nextToken();
			if (t.type != TokenType.PERIOD)
				throw new Exception(". expected: " + t);
			
			LemmaCommand lemma = lemmaCommands.peek();
			lemma.completeFlag = true;
			lemma.endTextPosition = baseTextPosition + t.ch + 1; 

			// Switch the mode
			mode = LEMMA_MODE;
			return;
		}
		
		// Translate the command
		String cmd = node.toHOLCommand(getContext());
		String rawCmd = "(hd o e)(" + cmd + ")";
		runCommand(rawCmd);
	}
	
	
	/**
	 * Interprets commands in the "lemma" mode
	 */
	private void processLemmaMode(TreeBuilder builder) throws Exception {
		LemmaNode lemma = builder.parseLemma();
		String rawCmd = "(hd o g)(" + lemma.getGoalText() + ")";
		runCommand(rawCmd);
		
		// Switch the mode
		mode = PROOF_MODE;
	}
	
	/**
	 * Reverts the last command and returns the absolute position in the text
	 * of the end of the second to the last command
	 */
	public int revertOneCommand() {
		int pos = revertOne();
		getAndUpdateState();
		return pos;
	}

	
	
	/**
	 * Reverts the last command and returns the absolute position in the text
	 * of the end of the second to the last command
	 */
	private int revertOne() {
		CommandInfo lastCmd = null;
		
		if (proofCommands.size() > 0) {
			lastCmd = proofCommands.pop(); 
		}
		else {
			if (lemmaCommands.size() > 0) {
				LemmaCommand lemma = lemmaCommands.pop();
				// Switch the mode if necessary
				if (!lemma.completeFlag)
					mode = LEMMA_MODE;
				
				lastCmd = lemma;
			}
		}
		
		if (lastCmd == null)
			return 0;

		// Revert the last command
		lastCmd.revert();
		
		// Get the new last command
		lastCmd = getLastCommand();
		if (lastCmd == null)
			return 0;
		
		return lastCmd.endTextPosition;
	}
	
	
	/**
	 * Reverts all commands up to the given absolute position in the script text
	 */
	public int revert(int pos) {
		int endPos = pos;
		
		// Iterate through proof commands first
		while (proofCommands.size() > 0) {
			CommandInfo cmd = proofCommands.peek();
			if (cmd.endTextPosition < pos) {
				getAndUpdateState();
				return endPos;
			}
			
			endPos = revertOne();
		}
		
		// Iterate through lemma commands next
		while (lemmaCommands.size() > 0) {
			CommandInfo cmd = lemmaCommands.peek();
			if (cmd.endTextPosition < pos)
				break;
			
			endPos = revertOne();
		}
		
		getAndUpdateState();
		return endPos;
	}
	
	
	/**
	 * Interprets the script.
	 * Returns the number of characters interpreted before the first error (if any)
	 */
	public int interpret(String text) {
		// Reset the error
		error = null;
		
		// Initialize the scanner first
		scanner = new Scanner(new StringReader(text));
		TreeBuilder builder = new TreeBuilder(scanner);
		
		// Set up the base text position
		setBaseTextPosition();
		
		try {
			while (true) {
				if (scanner.peekToken().type == TokenType.EOF)
					break;
				
				switch (mode) {
				// Proof
				case PROOF_MODE:
					processProofMode(builder);
					break;
			
				// Lemma
				case LEMMA_MODE:
					processLemmaMode(builder);
					break;
				}
			}
		}
		catch (Exception e) {
			System.err.println(e.getMessage());
			error = e;
		}
		
		CommandInfo lastCmd = getLastCommand();
		if (lastCmd == null)
			return 0;
		
		return lastCmd.endTextPosition - baseTextPosition;
	}
}
