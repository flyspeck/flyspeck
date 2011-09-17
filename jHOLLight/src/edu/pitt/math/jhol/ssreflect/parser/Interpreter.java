package edu.pitt.math.jhol.ssreflect.parser;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.Stack;

import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.Goalstate;
import edu.pitt.math.jhol.ssreflect.parser.tree.GoalContext;
import edu.pitt.math.jhol.ssreflect.parser.tree.LemmaNode;
import edu.pitt.math.jhol.ssreflect.parser.tree.Node;
import edu.pitt.math.jhol.ssreflect.parser.tree.RawNode;
import edu.pitt.math.jhol.ssreflect.parser.tree.SectionHypothesisNode;
import edu.pitt.math.jhol.ssreflect.parser.tree.SectionNode;
import edu.pitt.math.jhol.ssreflect.parser.tree.SectionVariableNode;
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
	
	// Mode constants
	private final static int PROOF_MODE = 1;
	private final static int GLOBAL_MODE = 2;
	
	// Information about all executed commands
	private final Stack<GlobalCommand> globalCommands;
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
		// The command itself
		public final Node command;
		
		// The position of the last character of the command in the script text
		public int endTextPosition;
		
		/**
		 * Protected constructor
		 */
		protected CommandInfo(Node command, int endTextPosition) {
			assert(command != null);
			this.command = command;
			this.endTextPosition = endTextPosition;
		}
		
		// Reverts the command
		// Returns true on success
		abstract boolean revert();
		
		@Override
		public String toString() {
			return command.toString() + "[" + endTextPosition + "]";
		}
	}
	
	// A command in the "global" mode
	private class GlobalCommand extends CommandInfo {
		GlobalCommand(Node command, int endTextPosition) {
			super(command, endTextPosition);
		}
		
		@Override
		boolean revert() {
			// By default, do nothing
			return true;
		}
	}
	
	// A command for starting and ending a section
	private class SectionCommand extends GlobalCommand {
		private final SectionNode section;
		
		SectionCommand(SectionNode section, int endTextPosition) {
			super(section, endTextPosition);
			this.section = section;
		}
		
		@Override
		boolean revert() {
			if (!section.isStartSection())
				return true;
			
			// Close the started section
			try {
				caml.runCommand("end_section \"" + section.getName() + "\";;");
			}
			catch (Exception e) {
				e.printStackTrace();
				return false;
			}
			
			return true;
		}
	}
	
	// A lemma description command
	private class LemmaCommand extends GlobalCommand {
		// The lemma description
		private final LemmaNode lemma;
		// If true, then the proof of the lemma has been completed
		public boolean completeFlag;
		
		LemmaCommand(LemmaNode lemma, int endTextPosition) {
			super(lemma, endTextPosition);
			this.lemma = lemma;
			this.completeFlag = false;
		}
		
		public String getLemmaName() {
			return lemma.getName();
		}
		
		boolean revert() {
			// TODO: undefine the lemma object 
			return true;
		}
	}
	
	// A command in the "proof" mode
	private class ProofCommand extends CommandInfo {
		ProofCommand(Node command, int endTextPosition) {
			super(command, endTextPosition);
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
		this.mode = GLOBAL_MODE;
		this.state = null;
		
		this.globalCommands = new Stack<GlobalCommand>();
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
	private GoalContext getContext() {
		if (state == null || state.numberOfGoals() == 0)
			return null;
		
		GoalContext context = new GoalContext(state.getGoal(0));
		return context;
	}
	
	
	/**
	 * Updates the goal state
	 * @throws Exception
	 */
	private void updateState(Goalstate newState) {
		if (newState == null) {
			if (state == null)
				return;
		}
		else {
			if (newState.equals(state))
				return;
		}
		
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
	 * Runs the command given by the syntax tree node and saves it in an appropriate stack.
	 * The command will be not executed if there is no '.' after the command
	 * in the text.
	 */
	private void runCommand(Node nodeCmd) throws Exception {
		// .
		Token t = scanner.nextToken();
		if (t.type != TokenType.PERIOD)
			throw new Exception(". expected: " + t);
		
		String rawCmd = nodeCmd.toHOLCommand(getContext());
		if (mode == PROOF_MODE) {
			rawCmd = "(hd o e) (" + rawCmd + ")";
			CamlObject result = caml.execute(rawCmd, CamlType.GOAL_STATE);
			if (result == null)
				throw new Exception("Null result");
		}
		else {
			rawCmd += ";;";
			// FIXME: If the command fails, then no error message will be reported
			caml.runCommand(rawCmd);
		}
		
		// Save the command in one of two stacks
		
		// Compute the end position of the command in the script text
		int end = baseTextPosition + t.ch + 1;
		
		switch (mode) {
		// Proof
		case PROOF_MODE:
			proofCommands.push(new ProofCommand(nodeCmd, end));
			break;
			
		// Global
		case GLOBAL_MODE:
			GlobalCommand cmd = null;
			// Lemma
			if (nodeCmd instanceof LemmaNode)
				cmd = new LemmaCommand((LemmaNode) nodeCmd, end);
			// Section
			else if (nodeCmd instanceof SectionNode)
				cmd = new SectionCommand((SectionNode) nodeCmd, end);
			else if (nodeCmd instanceof RawNode || 
					nodeCmd instanceof SectionHypothesisNode ||
					nodeCmd instanceof SectionVariableNode)
				cmd = new GlobalCommand(nodeCmd, end);
			else
				throw new Exception("Unexpected global command: " + nodeCmd);
			
			globalCommands.push(cmd);
			break;
		}
	}
	
	
	/**
	 * Returns the last command saved in the stack
	 */
	private CommandInfo getLastCommand() {
		if (proofCommands.size() > 0)
			return proofCommands.peek();

		if (globalCommands.size() > 0)
			return globalCommands.peek();
		
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
			// Remove all proof commands and modify the previous lemma command
			proofCommands.clear();
			if (globalCommands.size() == 0)
				throw new Exception("No lemma corresponding to the proof");
			
			// Should be .
			Token t = scanner.nextToken();
			if (t.type != TokenType.PERIOD)
				throw new Exception(". expected: " + t);
			
			// This conversion should succeed
			LemmaCommand lemma = (LemmaCommand) globalCommands.peek();
			lemma.completeFlag = true;
			lemma.endTextPosition = baseTextPosition + t.ch + 1;
			
			// TODO: do not save the result if the proof is aborted
			String saveCmd = "let " + lemma.getLemmaName() + " = end_section_proof();;";
			caml.runCommand(saveCmd);

			// Switch the mode
			mode = GLOBAL_MODE;
			return;
		}
		
		// Translate the command
		runCommand(node);
		getAndUpdateState();
	}
	
	
	/**
	 * Interprets commands in the "global" mode
	 */
	private void processGlobalMode(TreeBuilder builder) throws Exception {
		Node node = builder.parseGlobal();
		runCommand(node);
		
		// Switch the mode after the lemma 
		if (node instanceof LemmaNode) {
			getAndUpdateState();
			mode = PROOF_MODE;
		}
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
			if (globalCommands.size() > 0) {
				GlobalCommand cmd = globalCommands.pop();
				// Switch the mode if necessary
				if (cmd instanceof LemmaCommand && !((LemmaCommand) cmd).completeFlag)
					mode = GLOBAL_MODE;
				
				lastCmd = cmd;
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
		while (globalCommands.size() > 0) {
			CommandInfo cmd = globalCommands.peek();
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
			
				// Global
				case GLOBAL_MODE:
					processGlobalMode(builder);
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
