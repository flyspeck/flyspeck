package edu.pitt.math.jhol.irc;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import org.jibble.pircbot.PircBot;

import bsh.EvalError;
import bsh.Interpreter;

public class EchoBot extends PircBot {

	private String owner;
	private Interpreter interpreter;
	public EchoBot() throws EvalError {
		interpreter = new Interpreter();
		interpreter.set("bot", this);
		this.setName("EchoBot");
	}

	public String setOwner(String owner){
		return this.owner = owner;
	}
	
	public void message(String message){
		this.sendMessage(owner, message);
	}
	
	/**
	 * @param args
	 * @throws EvalError 
	 */
	public static void main(String[] args) throws EvalError {
		EchoBot bot = new EchoBot();
		
		bot.setVerbose(true);
		
		
		
	//server,channel,owner
		
		BufferedReader in
		   = new BufferedReader(new InputStreamReader(System.in));
		
		bot.setMessageDelay(0);
		 
		
		while(true){
			try {
				bot.interpreter.eval( in.readLine());
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			
		}

	}

}
