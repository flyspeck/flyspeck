package edu.pitt.math.jhol.irc;



import org.apache.commons.daemon.Daemon;
import org.apache.commons.daemon.DaemonContext;
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

	@Override
	public void init(DaemonContext arg0) throws DaemonInitException, Exception {
		
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
			holbots[i] = new HOLBot(prefix + i , server);
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
