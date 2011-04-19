package edu.pitt.math.jhol.irc;



import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.daemon.Daemon;
import org.apache.commons.daemon.DaemonContext;
import org.apache.commons.daemon.DaemonController;
import org.apache.commons.daemon.DaemonInitException;

import bsh.EvalError;

public class HOLDaemon implements Daemon {

	/*
	 * public String setOwner(String owner){ return this.owner = owner; }
	 * 
	 * public void message(String message){ this.sendMessage(owner, message); }
	 */
	
	private int count;
	private String server;
	private String prefix;
private HOLBot[] holbots;
private DaemonController controller;
	
	/**
	 * @param args
	 * @throws EvalError
	 */
	/*
	 * public static void main(String[] args) throws EvalError { HOLDaemon bot =
	 * new HOLDaemon();
	 * 
	 * bot.setVerbose(true);
	 * 
	 * 
	 * 
	 * //server,channel,owner
	 * 
	 * BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
	 * 
	 * bot.setMessageDelay(0);
	 * 
	 * 
	 * while(true){ try { bot.interpreter.eval( in.readLine()); } catch
	 * (IOException e) { // TODO Auto-generated catch block e.printStackTrace();
	 * }
	 * 
	 * 
	 * }
	 * 
	 * }
	 */
	
	@Override
	public void destroy()  {
		// TODO Auto-generated method stub
		
		for (int i = 0 ; i < count; i++){
			
			holbots[i].dispose();
		}
	}
	
	public void restart(int n){
		if (holbots[n] != null)
			holbots[n].dispose();
		holbots[n] = new HOLBot(prefix , n , server, this);
	}
	
	public void update(){
		List<String> l = new ArrayList<String>();
		l.add("svn");
		l.add("update");
		
		ProcessBuilder tmp = new ProcessBuilder(l);
		Process p = null;
		try {
			p = tmp.start();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		p.exitValue();
		l.clear();
		l.add("ant");
		try {
			p = tmp.start();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		p.exitValue();
		try {
			this.stop();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		controller.reload();
	}

	@Override
	public void init(DaemonContext arg0) throws DaemonInitException, Exception {
		this.controller = arg0.getController();
		String[] argv = arg0.getArguments();
		prefix = argv[0];
		server = argv[1];
		count  = Integer.parseInt(argv[2]);
		//System.out.println(prefix);
		//System.out.println(server);
		//S/ystem.out.println(count);
		//nick prefix
		//number of instances
		//server
		
		holbots = new HOLBot[count];
		
		//this.setName("holbot" + count);
		
		// channel = "#hol";
		
	}

	@Override
	public void start() throws Exception {
		// TODO Auto-generated method stub
		
		
		
		
		for (int i = 0; i < count; i++){
			restart(i);
		}
		
		
	
	}
	
	

	@Override
	public void stop() throws Exception {
		// TODO Auto-generated method stub
		
		for (int i = 0 ; i < count; i++){
			holbots[i].disconnect();
			
		}
		
		
		
	}

}
