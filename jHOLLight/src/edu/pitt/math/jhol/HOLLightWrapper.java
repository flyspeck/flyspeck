//Object for holding hol process
package edu.pitt.math.jhol;

import java.text.ParseException;
import java.util.Set;
import java.util.TreeSet;

import java.io.*;
import java.lang.reflect.Array;




import org.jibble.pircbot.IrcException;
import org.jibble.pircbot.NickAlreadyInUseException;
import org.jibble.pircbot.PircBot;

import edu.pitt.math.jhol.core.parser.Parser;



import bsh.EvalError;


public class HOLLightWrapper extends PircBot {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	

	// variable to keep track of the theorem count
	private  int numHolTheorems;

	// variable to hold all the theorems
	private  Set<String> holTheorems;
	private  bsh.Interpreter interpreter;
	
	//private  String user;
	//private  String server;
	//private  BufferedReader bufInput;
	//private  JTextPane goalPane;
	//private  Thread taskThread;
	
	private BufferedWriter out;

	
	//private boolean threadSuspended;



	private String botName;



	protected void eval(String evalStr) throws EvalError {
		interpreter.eval(evalStr);
	}

	

	
	public HOLLightWrapper(String botName, String myName, String server,BufferedWriter out) {
		//this.in = in;
		this.out =out;
		//this.server = server;
		this.setName(myName);
		this.botName = botName;
		
	
		
/*	private class SimpleThreadFactory implements ThreadFactory {
		   
		
		public Thread newThread(Runnable r) {
		    System.out.println("Starting taskThread");
			taskThread =  Executors.defaultThreadFactory().newThread(r);
			return taskThread;
		   }
		 }
	*/
	
		try {
			this.connect(server);
		} catch (NickAlreadyInUseException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IrcException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		this.joinChannel("#hol");
		this.setMessageDelay(0);
		this.interpreter = new bsh.Interpreter();
		try {
			interpreter.set("hol", this);
		} catch (EvalError e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		

		
		//numHolTheorems = 0;
		//holTheorems = new TreeSet<String>();
		
		
		
		
	}


	protected void onMessage(String chan, String sender, String login, String hostname, String message){
		if (out !=null && sender.equals( botName) && chan.equals("#hol") ){
			try {
				out.write(message);
				out.newLine();
				out.flush();
				try {
					out.write(Parser.parse(message).toString());
					out.newLine();
					out.flush();
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		if (this.getOutgoingQueueSize() == 0){
			synchronized(this){
				this.notifyAll();
		}
		}
	}

	public String runCommand (String cmd){
		this.sendMessage("#hol", botName + " eval " + cmd);
		throw new RuntimeException("FIX ME");
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

	



	private static String getLine(BufferedReader br) {

		StringBuilder sb = new StringBuilder();
		int c;
		try {
			while ( (c = br.read()) != -1) {
				//System.out.println(c);
				if (c == 10)
					return sb.toString();
				
				sb.appendCodePoint(c);
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}

	/*public void run() {



		String output = (runCommand("Sys.command(\"exit $PPID\");;"));

		this.holIsEchoing = (output.charAt(0) == 'S');
		if (isEchoing())
			output = (runCommand("Sys.command(\"exit $PPID\");;"));
		int lowByte = HOLLightWrapper.parseForInteger(output);
		int highByte = HOLLightWrapper
				.parseForInteger(runCommand("Sys.command \"exit $(($PPID / 256))\";;"));

		int pid = highByte * 256 + lowByte;

		this.holPid = pid;

		

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
		try {
			SwingUtilities.invokeAndWait(new Runnable() {
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
		} catch (InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		} catch (InvocationTargetException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

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

	
*/
	
	/*public  Future<String> runBackgroundCommand(String command) {
		HOLTask task = new HOLTask(command);
		es.submit(task);
		return task;
	}*/

	
	
	
	/*private class HOLTask extends SwingWorker<String, Character> {

		
		private String command;
		

		public HOLTask(String command) {
			this.command = command;

		}

		
		
		private String flushOutput(boolean flag) throws IOException {

			StringBuilder evalStr = new StringBuilder();
			StringBuilder str = new StringBuilder();
			StringBuilder suppressedOutput = new StringBuilder();
			char c;
			if (isEchoing()) {
				for (int i = 0; i < command.length() + 1; i++)
					c = (char) read();
			}
			do {
				//if (threadSuspended) {
                    synchronized(this) {
                        while (threadSuspended)
							try {
								wait();
							} catch (InterruptedException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
                    }
                }//Comment if thread suspended block
			
				//if (isInterrupted()){
					interrupt.start();
					StringBuilder sb = new StringBuilder();
					while(sb.indexOf("Interrupted.") == -1)
					{
						sb.append(c = (char) read());
					}
					str.append(sb.toString());
					if (!flag)
						publish(sb.toString());
					HOLLightWrapper.this.acknowledgeInterrupt();
					continue;
				}//Comment if is interrupted block
				
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
			boolean flag = command.charAt(command.length() - 1) != '\n';
			if (flag) {
				command = command + "\n";
				// printHTML(cmd);
			}// If we generated the command, dont let them know

			try {
				write(command);
				flush();
				
				return flushOutput(flag);

			} catch (IOException e) {
				printErr(e);

				return null;
			}
		}
	}
*/
	
	
	
	public static void main(String[] args){
		//javax.swing.SwingUtilities.invokeLater(
			//	  new Runnable() {
				//    public void run() {
		
		if (args.length < 3)
			System.exit(-1);
		
				    	BufferedReader in
				    	   = new BufferedReader(new InputStreamReader(System.in));
				    	BufferedWriter out
				    	= new BufferedWriter(new OutputStreamWriter(System.out));
				    	HOLLightWrapper test = new HOLLightWrapper(args[1], args[0], args[2], out);
				    	String cmd;
				    	
				    	
							while(null != (cmd = getLine(in)))
							{
								test.runCommand(cmd);
							}
							
							synchronized(test){
								try {
									
									test.wait();
									
								} catch (InterruptedException e) {
									// TODO Auto-generated catch block
									e.printStackTrace();
								}
							}
							
							test.disconnect();
							test.dispose();
							test = null;
							
						} 
				//
				 //   }
					
				 // }); 	
	
	
	public Set<String> getTheoremList() {
		return new TreeSet<String>(this.holTheorems);
	}




	public void interrupt() {
		// TODO Auto-generated method stub
		
	}
	
}
