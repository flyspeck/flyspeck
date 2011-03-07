package edu.pitt.math.jhol.irc;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

import org.jibble.pircbot.IrcException;
import org.jibble.pircbot.NickAlreadyInUseException;
import org.jibble.pircbot.PircBot;

public class EchoBot extends PircBot {

	public EchoBot() {
		this.setName("EchoBot");
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		EchoBot bot = new EchoBot();
		
		bot.setVerbose(true);
		
		try {
			bot.connect("charizard.zapto.org");
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
		
		bot.joinChannel("#hol");
		
		BufferedReader in
		   = new BufferedReader(new InputStreamReader(System.in));
		 
		String line = "";
		while(line != null){
			try {
				line = in.readLine();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			bot.sendMessage("#hol", line);
		}

	}

}
