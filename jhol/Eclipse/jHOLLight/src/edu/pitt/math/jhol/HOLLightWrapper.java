//Object for holding hol process
package edu.pitt.math.jhol;

import java.text.ParseException;
import java.util.*;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.io.*;
import java.lang.reflect.Array;

import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JTextPane;
import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultStyledDocument;
import javax.swing.text.StyledDocument;

import bsh.EvalError;
import bsh.util.JConsole;

public class HOLLightWrapper extends JConsole {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private volatile BufferedWriter bin;
	private volatile BufferedReader bout;
	private volatile Process proc;
	private volatile ExecutorService es;

	private volatile ProcessBuilder interrupt;
	private volatile Boolean holIsEchoing;
	private volatile int holPid;

	// variable to keep track of the theorem count
	private volatile int numHolTheorems;

	// variable to hold all the theorems
	private volatile Set<String> holTheorems;
	private volatile bsh.Interpreter interpreter;
	private volatile JTextPane consoleTextPane;
	private volatile String user;
	private volatile String server;
	private volatile BufferedReader bufInput;
	private volatile JTextPane goalPane;

	public Set<String> getTheoremList() {
		return new TreeSet<String>(this.holTheorems);
	}

	protected void eval(String evalStr) throws EvalError {
		interpreter.eval(evalStr);
	}

	protected Integer getPID() {
		return holPid;
	}

	protected boolean isEchoing() {
		return (holIsEchoing != null) && holIsEchoing;
	}

	public void kill() {
		proc.destroy();
	}

	public void interrupt() {
		try {
			interrupt.start();
		} catch (IOException e) {
			printErr(e);

		}
	}

	private void printErr(IOException e) {
		printErr("Console: I/O Error: " + e);
	}

	protected void printErr(String s) {
		print(s + "\n", Color.red);
	}

	protected void write(String s) throws IOException {
		bin.write(s);
	}

	protected void flush() throws IOException {
		bin.flush();
	}

	public JTextPane getGoalPane(){
		return goalPane;
	}

	public HOLLightWrapper() throws IOException, EvalError{
		this(null,null);
	}
	
	public void connect(String user, String server) throws IllegalArgumentException, IOException{
		if (proc != null)
			throw new IllegalArgumentException("Already connected");
		List<String> command = new ArrayList<String>();
		command.add("ssh");
		command.add("-tt");
		command.add(user + "@" + server);
		command.add("hol_light");
		ProcessBuilder pb = new ProcessBuilder(command);
		pb.redirectErrorStream(true);
		proc = pb.start();
		bin = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream()));
		bout = new BufferedReader(new InputStreamReader(proc.getInputStream()));
		
		this.user = user;
		this.server = server;
		
		notifyES();
	}
	
	public HOLLightWrapper(String user, String server) throws IOException,
			EvalError {
		

		goalPane = new GoalPane();
		
		this.interpreter = new bsh.Interpreter();
		interpreter.set("hol", this);
		

		holIsEchoing = null;

		holPid = 0;
		interrupt = null;
		numHolTheorems = 0;
		holTheorems = new TreeSet<String>();
		consoleTextPane = (JTextPane) getViewport().getView();	
		Font font = new Font("Monospaced", Font.PLAIN, 12);
		this.consoleTextPane.setFont(font);
		bufInput = new BufferedReader(getIn());
		es = Executors.newSingleThreadExecutor();
consoleTextPane.setEditable(false);
		this.setPreferredSize(new Dimension(550,350));
		if (user != null && server != null)
			connect(user, server);
		
		
	}

	private synchronized void guardedES() {
		while (es == null) {
			try {
				wait();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}

	}

	private synchronized void notifyES() {

		notifyAll();
	}

	public boolean ready() throws IOException {
		return bout.ready();
	}

	// method for running multiple hol commands at once
	public void runHOLCommands(String cmds) {
		String[] array = cmds.split("\n");

		for (int i = 0; i < Array.getLength(array); i++) {
			runCommand(array[i]);
		}
	}

	// query hol for the number of theorems in the system
	private Integer getNumHolTheorems() {
		String output = runCommand("List.length !theorems;;");
		// System.out.println(output);
		return parseForInteger(output);
	}

	public static Integer parseForInteger(String rawOutput) {
		int equalsIndex = rawOutput.indexOf('=');
		rawOutput = rawOutput.substring(equalsIndex + 2);
		int newlineIndex = rawOutput.indexOf('\n');
		rawOutput = rawOutput.substring(0, newlineIndex);
		// System.out.println(rawOutput);
		return Integer.decode(rawOutput.trim());
	}

	public static String parseForString(String rawOutput) throws ParseException {
		int beginIndex = rawOutput.indexOf('\"') + 1;
		int endIndex = 0;
		for (int i = beginIndex; i < rawOutput.length(); i++) {
			if (rawOutput.charAt(i) == '\\') {
				i++;
				continue;
			}
			if (rawOutput.charAt(i) == '\"') {
				endIndex = i;
				break;
			}

		}
		if (beginIndex == 0)
			throw new ParseException("Missing opening \".", 0);
		if (endIndex == 0)
			throw new ParseException("Missing closing \".",
					rawOutput.length() - 1);
		return rawOutput.substring(beginIndex, endIndex);
	}

	// method to keep theorem list up to date
	public void updateHolTheorems() throws ParseException {
		if (numHolTheorems != getNumHolTheorems()) {
			numHolTheorems = getNumHolTheorems();

			String bangTheorems = runCommand("String.concat \" \" ((fst o List.split)!theorems);;");
			String[] bangTheorems2;

			bangTheorems2 = parseForString(bangTheorems).split(" ");

			for (int i = 0; i < Array.getLength(bangTheorems2); i++) {
				holTheorems.add(bangTheorems2[i]);
			}
		}
	}

	// Method for printing to the console
	void printHTML(String html) {
		while (html.indexOf("<HTML>") != -1) {
			int start = html.indexOf("<HTML>");
			// console.print(html.substring(0, start));//Print any text that
			// occurs before the HTML
			int end = html.indexOf("</HTML>");
			String htmlText = html.substring(start, end + 7);
			JLabel tmpLabel = htmlToJLabel(htmlText);

			((JTextPane) consoleTextPane).insertComponent(tmpLabel);
			html = html.substring(end + 7, html.length());
		}
		print(html);
	}

	// begin low level functions
	private static int asciiToDecimal(int c) {
		if (97 <= c) {
			c = c - 87;
		} else {
			c = c - 48;
		}
		return c;
	}

	private int getChar() {
		BufferedReader br = bufInput;
		char[] tmp = new char[6];
		for (int i = 0; i < 6; i++)
			try {
				tmp[i] = (char) br.read();
			} catch (IOException e) {

				e.printStackTrace();
			}
		int result = 0;
		int factor = 1;
		for (int i = 5; i >= 2; i--) {
			result += factor * asciiToDecimal(tmp[i]);
			factor *= 16;
		}
		return result;
	}

	protected String getLine() {

		StringBuilder sb = new StringBuilder();
		while (true) {
			int c = getChar();
			if (c == 10)
				break;
			
			sb.appendCodePoint(c);
		}
		return sb.toString();
	}

	public void run() {

		guardedES();
final StringBuilder sb = new StringBuilder();
		try {
			char c;
			while ((c = (char) read()) != '#') {
				sb.append(c);
			}
			sb.append(c);
			c = (char) read();
			sb.append(c);
		} catch (IOException e1) {
			printErr(e1);
		}

		String output = (runCommand("Sys.command(\"exit $PPID\");;"));

		this.holIsEchoing = (output.charAt(0) == 'S');
		if (isEchoing())
			output = (runCommand("Sys.command(\"exit $PPID\");;"));
		int lowByte = HOLLightWrapper.parseForInteger(output);
		int highByte = HOLLightWrapper
				.parseForInteger(runCommand("Sys.command \"exit $(($PPID / 256))\";;"));

		int pid = highByte * 256 + lowByte;

		this.holPid = pid;

		// ssh ${USER}@${SERVER} kill -2 $1
		List<String> command = new ArrayList<String>();
		command.add("ssh");
		command.add("-tt");
		command.add(user + "@" + server);
		command.add("kill");
		command.add("-2");
		command.add(getPID().toString());

		ProcessBuilder kill = new ProcessBuilder(command);
		kill.redirectErrorStream(true);

		interrupt = kill;

		// run commands in hol to initialize the data pipe
		runHOLCommands("let java cmd = ignore(Sys.command(String.concat  \" \" [\"echo \\\"@\";String.escaped cmd;\"\\\"\"]));;\n"
				+ "let suffices_to_prove q tac = SUBGOAL_THEN q (fun th -> MP_TAC th THEN tac);;\n"
				+ "let trivial = MESON_TAC[];;\n"
				+ "let induction = INDUCT_TAC;;\n"
				+ "let using ths tac = MAP_EVERY MP_TAC ths THEN tac;;\n"
				+ "let so constr arg tac = constr arg (FIRST_ASSUM MP_TAC THEN tac);;\n"
				+ "let g goal = (java o (fun () -> \"global.hol.beginTopGoal();\") o ignore o g) goal;;\n"
				+ "let e tactic = (java o (fun () -> \"global.hol.updateTopGoal();\") o ignore o e) tactic;;\n"
				+ "let b () = (java o (fun () -> \"global.hol.updateTopGoal();\") o ignore o b) ();;\n"
				+ "let set_goal (asl,goal) = (java o (fun () -> \"global.hol.beginTopGoal();\") o ignore o set_goal) asl,goal;;\n"
				+ "let r int = (java o (fun () -> \"global.hol.updateTopGoal();\") o ignore o r) int;;");

		String newprinterML = Utilities.readFile("newprinter.ml");

		runHOLCommands(newprinterML);

		// update the theorem list
		try {
			updateHolTheorems();
		} catch (ParseException e) {

			printErr("Error in " + HOLLightWrapper.class.toString()
					+ "in run(): " + e);
		}
		SwingUtilities.invokeLater(new Runnable() {
			public void run() {
				
				HOLLightWrapper.this.consoleTextPane.setEditable(true);
				print(sb.toString());
				consoleTextPane.addKeyListener(new KeyAdapter(){
					
				      
			        public void keyPressed(KeyEvent e){
			        	if (!SwingUtilities.isEventDispatchThread())
			        		throw new RuntimeException("EDT@");
			        if (e.isControlDown() && e.getKeyCode() == KeyEvent.VK_C){
			        	HOLLightWrapper.this.interrupt();
			        }
			        
			        
			        }
			    });
			}
		});

		// super.run();
		// Main Loop
		List<String> cmdList = new LinkedList<String>();
		try {
			while (true) {
				do {
					// in case someone pastes more than one command into the
					// buffer
					
					String line = getLine();
					
					cmdList.add(line);
				} while (bufInput.ready());
				while (cmdList.size() != 0) {
					runCommand(((LinkedList<String>) cmdList).removeFirst()
							+ "\n");
				}
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

	protected int read() throws IOException {
		if (SwingUtilities.isEventDispatchThread())
			throw new RuntimeException("EDT");
		return bout.read();
	}

	protected String readLine() throws IOException {
		return bout.readLine();
	}

	public synchronized Future<String> runBackgroundCommand(String command) {
		HOLTask task = new HOLTask(command);
		es.submit(task);
		return task;
	}

	public String runCommand(String string) {

		try {
			return runBackgroundCommand(string).get();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (ExecutionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}

	private class HOLTask extends SwingWorker<String, Character> {

		private boolean flag;
		private String command;

		public HOLTask(String command) {
			this.command = command;

		}

		private String flushOutput() throws IOException {

			StringBuilder evalStr = new StringBuilder();
			StringBuilder str = new StringBuilder();
			StringBuilder suppressedOutput = new StringBuilder();
			char c;
			if (isEchoing()) {
				for (int i = 0; i < command.length() + 1; i++)
					c = (char) read();
			}
			do {

				c = (char) read();

				// System.out.print(c);
				if (str.length() == 0 && c == '@') {
					evalStr.append(readLine());
					evalStr.append(';');
					continue;
				}

				if (c == 65535) {

					suppressedOutput.append(str.toString());

					printErr("hol_light: EOF reached.");
					break;
				}
				str.append(c);
				 if (!flag)
				this.publish(c);
				if (c == 10) {

					suppressedOutput.append(str.toString());
					str = new StringBuilder();
					continue;
				}

			} while (!(str.length() == 2
					&& (str.charAt(0) == '#' || str.charAt(0) == ' ')
					&& str.charAt(1) == ' ' && !ready()));

			suppressedOutput.append(str.toString());
			String result = suppressedOutput.toString();
			try {
				eval(evalStr.toString());
			} catch (EvalError e) {

				printErr("Java command failed: " + e);
			}
			return result;
		}

		protected void process(List<Character> chunks) {
			for (Character c : chunks) {
				print(c);
			}
		}

		protected String doInBackground() {

			if (command.length() == 0)
				return null;
			flag = command.charAt(command.length() - 1) != '\n';
			if (flag) {
				command = command + "\n";
				// printHTML(cmd);
			}// If we generated the command, dont let them know

			try {
				write(command);
				flush();

				return flushOutput();

			} catch (IOException e) {
				printErr(e);

				return null;
			}
		}
	}

	private class GoalPane extends JTextPane {

		/**
		 * 
		 */
		private static final long serialVersionUID = 1L;

		public GoalPane() {
			super(new DefaultStyledDocument());
			setEditable(false);
		}

	}

	public void beginTopGoal() {

		updateTopGoal();
	}

	public void updateTopGoal() {

		JTextPane text = goalPane;
		text.setText("");
		StyledDocument doc = text.getStyledDocument();

		// Print "Goal: "
		String htmlString = getHTMLHeader("") + "<b>Goal: </b>"
				+ getHTMLFooter();
		JLabel label = htmlToJLabel(htmlString);
		text.insertComponent(label);

		// Line break
		try {
			doc.insertString(doc.getEndPosition().getOffset(), "\n", null);
		} catch (BadLocationException e) {

			e.printStackTrace();
		}
		text.setCaretPosition(doc.getLength());

		// Print top_goal
		String junk = runCommand("(snd o top_goal)();;");
		int junkInt = junk.indexOf("<HTML>");// DEBUG all html tag tests should
												// be case insensitive
		if (junkInt == -1)
			return;
		int junkEnd = junk.indexOf("</HTML>") + 7;
		junk = junk.substring(junkInt, junkEnd);
		label = htmlToJLabel(junk);
		text.insertComponent(label);

		// Line break
		try {
			doc.insertString(doc.getEndPosition().getOffset(), "\n\n", null);
		} catch (BadLocationException e) {

			e.printStackTrace();
		}
		text.setCaretPosition(doc.getLength());

		// Print "Assumptions: "
		htmlString = getHTMLHeader("") + "<b>Assumption(s): </b>"
				+ getHTMLFooter();
		label = htmlToJLabel(htmlString);
		text.insertComponent(label);

		// Line break
		try {
			doc.insertString(doc.getEndPosition().getOffset(), "\n", null);
		} catch (BadLocationException e) {

			e.printStackTrace();
		}
		text.setCaretPosition(doc.getLength());

		// Print the assumptions
		junk = runCommand("List.iter (fun x,y ->( ((fun ()->"
				+ "(print_string \"\\n\")) o  (fun () ->"
				+ "(((print_qterm o  concl) y)))) o print_string) (\"\""
				+ "))   ((fst o top_realgoal)());;");
		while (junk.indexOf("<HTML>") != -1) {
			junkInt = junk.indexOf("<HTML>");
			junkEnd = junk.indexOf("</HTML>") + 7;
			label = htmlToJLabel(junk.substring(junkInt, junkEnd));
			junk = junk.substring(junkEnd, junk.length());
			text.insertComponent(label);
			try {
				doc.insertString(doc.getEndPosition().getOffset(), "\n", null);
			} catch (BadLocationException e) {

				e.printStackTrace();
			}
			text.setCaretPosition(doc.getLength());
		}
	}

	static JLabel htmlToJLabel(String htmlText) {
		return new JLabel(htmlText, JLabel.LEFT);
	}

	static String getHTMLHeader(String title) {
		if (title == null)
			title = "";
		return "<HTML><HEAD><TITLE>" + title + "</TITLE></HEAD><BODY>";
	}

	static String getHTMLFooter() {
		return "</BODY></HTML>";
	}

	
	
	public static void main(String[] args){
		javax.swing.SwingUtilities.invokeLater(
				  new Runnable() {
				    public void run() {
					System.setProperty("apple.laf.useScreenMenuBar", "true");
					
					System.setProperty("com.apple.mrj.application.apple.menu.about.name", "HOL Terminal");
					
					System.setProperty("com.apple.mrj.application.growbox.intrudes", "false");
					
					System.setProperty("com.apple.macos.smallTabs", "true");
					
					HOLLightWrapper hol;
					try {
						hol = new HOLLightWrapper();
						//Create and set up the window.
						JFrame frame = new JFrame("HOL Terminal");
						frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
						frame.add(hol);

						
						//Display the window.
						frame.pack();
						frame.setVisible(true);
						hol.connectDialog( frame);
					    
						
					} catch (IOException e1) {
						// TODO Auto-generated catch block
						e1.printStackTrace();
					} catch (EvalError e1) {
						// TODO Auto-generated catch block
						e1.printStackTrace();
					}
					
				    }
					
				  }); 	

	
	}
	
	public void connectDialog(JFrame frame) throws IllegalArgumentException, IOException{
		String s = (String)JOptionPane.showInputDialog(
                frame,
                "Enter username",
                
                "Username",
                JOptionPane.PLAIN_MESSAGE,
                null,
                null,
                null);
		String t = (String)JOptionPane.showInputDialog(
                frame,
                "Enter hostname",
                
                "HOL Server",
                JOptionPane.PLAIN_MESSAGE,
                null,
                null,
                null);

//If a string was returned, say so.
if ((s != null) && (s.length() > 0) && (t != null) && (t.length() > 0)) {
connect(s,t);
}
else
throw new IllegalArgumentException("Bad Input");
	}
		
	
	
	
}
