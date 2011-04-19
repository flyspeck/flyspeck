package edu.pitt.math.jhol.irc;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import org.jibble.pircbot.IrcException;
import org.jibble.pircbot.NickAlreadyInUseException;
import org.jibble.pircbot.PircBot;



public class HOLBot extends PircBot implements  Runnable {

	// private String owner;
	// private Interpreter interpreter;
	
	private Process proc;
	private BufferedWriter bin;
	private BufferedReader bout;
	private int holPid;
	private ProcessBuilder interrupt;
	private String homeChannel;
	private String server;
	private String channel;
	private boolean sleeping;
	private ProcessBuilder pb;
	/*
	 * public String setOwner(String owner){ return this.owner = owner; }
	 * 
	 * public void message(String message){ this.sendMessage(owner, message); }
	 */
	
	private ExecutorService es;
	private int cellNumber;
	private HOLDaemon controller;
	
	
	
	
	public HOLBot(String nick, int n, String server, HOLDaemon holDaemon)  {
		// interpreter = new Interpreter();
		// interpreter.set("bot", this);
		homeChannel = "#hol";
		this.setName(nick + n);
		this.cellNumber = n;
		this.server = server;
		this.controller = holDaemon;
	
		es = Executors.newSingleThreadExecutor();
		
		this.setMessageDelay(0);// So we can output at fast rates
		this.setVerbose(true);// DEBUG
	
		holPid = 0;
		interrupt = null;
		
		// Config stuff goes here
		//String[] args = arg0.getArguments();
		//server = args[0];
		//if (server == null || server.length() == 0)
			//server = "charizard.zapto.org";
		
		
List<String> command = new ArrayList<String>();
		
		command.add("./hol");
		 pb = new ProcessBuilder(command);
		pb.redirectErrorStream(true);
		
		
		try {
			proc = pb.start();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	
		bin = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream()));
		bout = new BufferedReader(new InputStreamReader(proc.getInputStream()));
		

		
		
		es.submit(this);
		
		try {
			write("Sys.command \"stty -echo\";;\n");
			flush();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
		
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
		
	}

	public void dispose(){
		super.dispose();
		es.shutdown();
		proc.destroy();
	}
	
	protected void write(String s) throws IOException {
		bin.write(s);
	}

	protected void flush() throws IOException {
		bin.flush();
	}

	public boolean ready() throws IOException {
		return bout.ready();
	}

	protected int read() throws IOException {

		return bout.read();
	}

	protected void onMessage(String channel, String sender, String login, String hostname, String message){





		if (message.startsWith(this.getNick()) || message.startsWith("all")){



			//If we have been addressed
			int pos = message.indexOf(' ');
			message = message.substring(pos).trim();

			if (sleeping){
				if (message.startsWith("sleep")){
					sendMessage(channel, "Hibernating.");
				
				}
				if (message.startsWith("wake")){
					sleeping = false;
					sendMessage(channel, "Sentry mode activated.");
					
				}
			}else{

				if (message.startsWith("sleep")){
					sleeping = true;
					sendMessage(channel, "Sleep mode activated. (do '" + this.getNick() + " wake' to wake)");
					
				}
				if (message.startsWith("wake")){
					sleeping = false;
					sendMessage(channel, "Canvassing.");
					
				}

				//If this is the active channel[ and is an eval command
				if (message.startsWith("eval")){
					if (this.channel == null || this.channel.equals(channel)){
						pos = message.indexOf(' ');
						message = message.substring(pos).trim() + "\n";
						try {
							write(message);
							flush();
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}

					}else{
						this.sendMessage(channel, sender + " sorry but I am currently listening in " + this.channel);
					}
				}


				if (message.startsWith("help")){
					this.sendMessage(channel, sender + ", I am " + this.getNick() + ", a HOL Light toplevel bot");
					this.sendMessage(channel, "you can instruct me with the following commands:");
					this.sendMessage(channel, "eval       evaluate hol command");
					this.sendMessage(channel, "help       print help message");
					this.sendMessage(channel, "restart    restart the toplevel");
					this.sendMessage(channel, "sleep      go to sleep");
					this.sendMessage(channel, "wake       wake me up from sleep");
					this.sendMessage(channel, "interrupt  interrupt the toplevel");
					
					
				}
				if (message.startsWith("restart")){
					controller.restart(cellNumber);
				}
				if (message.startsWith("update")){
					controller.update();
					
				}

				if (message.startsWith("interrupt")){
					try {
						interrupt.start();
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}


			}


		}
	}

		protected String readLine() throws IOException {

			return bout.readLine();
		}

		/*
		 * public String setOwner(String owner){ return this.owner = owner; }
		 * 
		 * public void message(String message){ this.sendMessage(owner, message); }
		 */

		protected void onDisconnect(){
			boolean flag = false;
			do {
				try {
			
					flag = false;
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
			}while(flag);
			this.joinChannel(homeChannel);
		}
		protected void onConnect(){
			this.joinChannel(homeChannel);
		}

		public void run() {
			String line = "";
			while (line != null) {
				try {
					line = bout.readLine();
				//	line = line.substring(1).trim();
					if (channel == null)
						
					this.sendMessage(homeChannel, line);
					else
					this.sendMessage(channel, line);
					
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			//TODO restart the toplevel
		}

	}
