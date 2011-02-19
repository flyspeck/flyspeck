package edu.pitt.math.jhol;

import java.util.concurrent.*;
import edu.pitt.math.jhol.HOLLightWrapper;


public class HOLTask implements Callable<String>{

	
	private final HOLLightWrapper hol;
	private final String command;
	public HOLTask (HOLLightWrapper hol, String command){
		this.command = command;
		this.hol = hol;
	}
	

	@Override
	public String call() throws Exception {
		return hol.runCommand(command);
	}

}
