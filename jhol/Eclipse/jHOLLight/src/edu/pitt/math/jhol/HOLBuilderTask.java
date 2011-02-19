package edu.pitt.math.jhol;

import java.util.LinkedList;
import java.util.concurrent.Callable;

public class HOLBuilderTask implements Callable<HOLLightWrapper> {

	private HOLLightWrapper hol;
	
	protected HOLBuilderTask (HOLLightWrapper hol){
		if (hol.isBuilt())
			throw new IllegalArgumentException("This wrapper has already been built.");
		this.hol = hol;
	}
	
	@Override
	public HOLLightWrapper call() throws Exception {
	    
	    	String firstOutput = "";
	    	while(firstOutput.indexOf("#") == -1){
	    	    firstOutput += (hol.flushOutput());
	    	    //This is on another thread since this may block for a while
	    	}
	    	
	    	String output = (hol.runCommand("Sys.command(\"exit $PPID\");;"));
	        
	        	hol.setEcho(output.charAt(0) == 'S');
	        if (hol.isEchoing())
	        	output = (hol.runCommand("Sys.command(\"exit $PPID\");;"));
	        int lowByte = HOLLightWrapper.parseForInteger(output);
	        int highByte = HOLLightWrapper.parseForInteger(hol.runCommand("Sys.command \"exit $(($PPID / 256))\";;"));;
		    int pid = highByte * 256 + lowByte;
	        
	        hol.setPID (pid);
	    	
	    	LinkedList<String> command = new LinkedList<String>();
	        command.add("sig_int_hol_light");
	        command.add(hol.getPID().toString());
	        ProcessBuilder kill = new ProcessBuilder(command);
	        kill.redirectErrorStream(true);
	    
	        hol.setInterrupt(kill);
	        
	      //run commands in hol to initialize the data pipe
	        hol.runHOLCommands( 
	    		   "let java cmd = ignore(Sys.command(String.concat  \" \" [\"echo \\\"@\";String.escaped cmd;\"\\\"\"]));;\n" +
	    		   "let suffices_to_prove q tac = SUBGOAL_THEN q (fun th -> MP_TAC th THEN tac);;\n" +
	    		   "let trivial = MESON_TAC[];;\n" +
	    		   "let induction = INDUCT_TAC;;\n" +
	    		   "let using ths tac = MAP_EVERY MP_TAC ths THEN tac;;\n" +
	    		   "let so constr arg tac = constr arg (FIRST_ASSUM MP_TAC THEN tac);;\n" +
	    		   "let g goal = (java o (fun () -> \"global.framework.getGoalPane().beginTopGoal();\") o ignore o g) goal;;\n" +
	    		   "let e tactic = (java o (fun () -> \"global.framework.getGoalPane().updateTopGoal();\") o ignore o e) tactic;;\n" +
	    		   "let b () = (java o (fun () -> \"global.framework.getGoalPane().updateTopGoal();\") o ignore o b) ();;\n" +
	    		   "let set_goal (asl,goal) = (java o (fun () -> \"global.framework.getGoalPane().beginTopGoal();\") o ignore o set_goal) asl,goal;;\n" +
	    		   "let r int = (java o (fun () -> \"global.framework.getGoalPane().updateTopGoal();\") o ignore o r) int;;");
	        
	        //update the theorem list
	        hol.updateHolTheorems();
	        
	        hol.setBuilt();
	    return hol;
	}

}
