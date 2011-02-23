//Object for holding hol process
package edu.pitt.math.jhol;

import java.text.ParseException;
import java.util.*;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.awt.Color;
import java.awt.Component;
import java.awt.Font;
import java.io.*;
import java.lang.reflect.Array;

import javax.swing.JLabel;
import javax.swing.JTextPane;
import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;

import bsh.EvalError;
import bsh.util.JConsole;

public class HOLLightWrapper extends JConsole {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private  BufferedWriter bin;
	private  BufferedReader bout;
	private  Process proc;
	private ExecutorService es;

	private  ProcessBuilder interrupt;
	private  Boolean holIsEchoing;
	private  int holPid;

	// variable to keep track of the theorem count
	private  int numHolTheorems;

	// variable to hold all the theorems
	private  Set<String> holTheorems;
	private  bsh.Interpreter interpreter;
	private  Component consoleTextPane;
	private  String user;
	private  String server;

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

	public static HOLLightWrapper create(String user, String server, bsh.Interpreter interpreter) throws IOException{
		final HOLLightWrapper result = new HOLLightWrapper(user,server,interpreter);
		//new Thread(result).start();
		return result;
	}
	
    private HOLLightWrapper(String user, String server,
			bsh.Interpreter interpreter) throws IOException {
		List<String> command = new ArrayList<String>();
		command.add("ssh");
		command.add("-tt");
		command.add(user + "@" + server);
		command.add("hol_light");

		this.user = user;
		this.server = server;

		ProcessBuilder pb = new ProcessBuilder(command);
		this.interpreter = interpreter;
		pb.redirectErrorStream(true);

		holIsEchoing = null;

		holPid = 0;
		interrupt = null;
		numHolTheorems = 0;
		holTheorems = new TreeSet<String>();
		consoleTextPane = getViewport().getView();
		proc = pb.start();

		bin = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream()));
		bout = new BufferedReader(new InputStreamReader(proc.getInputStream()));
		Font font = new Font("Monospaced", Font.PLAIN, 12);
		this.consoleTextPane.setFont(font);
		es = Executors.newSingleThreadExecutor();
		
		
notifyES();
	}

    private synchronized void guardedES(){
    	while(es == null){
    		try {
				wait();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
    	}
    	
    }
    private synchronized void notifyES(){
    	
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
			JLabel tmpLabel = GoalPane.htmlToJLabel(htmlText);

			((JTextPane) consoleTextPane).insertComponent(tmpLabel);
			html = html.substring(end + 7, html.length());
		}
		print(html);
	}

	// begin low level functions
	public static int asciiToDecimal(int c) {
		if (97 <= c) {
			c = c - 87;
		} else {
			c = c - 48;
		}
		return c;
	}

	public int getChar() {
		Reader br = getIn();
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

	public String getLine() {

		StringBuilder sb = new StringBuilder();
		while (true) {
			int c = getChar();
			if (c == 10)
				break;
			sb.appendCodePoint(c);
		}
		return sb.toString();
	}

	public  void run() {
		
		
		
	guardedES();
		
		  
		  try {
			  while((char)read()!='#'){}
			  read();
		} catch (IOException e1) {
			printErr(e1);
		}
		 
		
		
		String output = (runCommand("Sys.command(\"exit $PPID\");;"));

		this.holIsEchoing = (output.charAt(0) == 'S');
		if (isEchoing())
			output = (runCommand("Sys.command(\"exit $PPID\");;"));
		int lowByte = HOLLightWrapper.parseForInteger(output);
		int highByte = HOLLightWrapper.parseForInteger(runCommand("Sys.command \"exit $(($PPID / 256))\";;"));
		
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
				+ "let g goal = (java o (fun () -> \"global.framework.getGoalPane().beginTopGoal();\") o ignore o g) goal;;\n"
				+ "let e tactic = (java o (fun () -> \"global.framework.getGoalPane().updateTopGoal();\") o ignore o e) tactic;;\n"
				+ "let b () = (java o (fun () -> \"global.framework.getGoalPane().updateTopGoal();\") o ignore o b) ();;\n"
				+ "let set_goal (asl,goal) = (java o (fun () -> \"global.framework.getGoalPane().beginTopGoal();\") o ignore o set_goal) asl,goal;;\n"
				+ "let r int = (java o (fun () -> \"global.framework.getGoalPane().updateTopGoal();\") o ignore o r) int;;");

		String newprinterML = Utilities.readFile("newprinter.ml");
	
		runHOLCommands(newprinterML);
	    
		
		// update the theorem list
		try {
			updateHolTheorems();
		} catch (ParseException e) {

			printErr("Error in " + HOLLightWrapper.class.toString()
					+ "in run(): " + e);
		}
		SwingUtilities.invokeLater(new Runnable()
		{
		    public void run()
		    {
		    	consoleTextPane.addKeyListener(new HOLKeyAdapter(HOLLightWrapper.this));
		    }           
		});  
		System.out.print("READY");
		super.run();

	}

	protected int read() throws IOException {

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
				for (int i = 0; i < command.length(); i++)
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

		protected void process(List<Character> chunks){
			for (Character c : chunks){
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
	
	
	
}
