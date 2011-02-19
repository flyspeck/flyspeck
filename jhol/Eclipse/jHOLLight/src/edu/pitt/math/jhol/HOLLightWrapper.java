//Object for holding hol process
package edu.pitt.math.jhol;

import java.text.ParseException;
import java.util.*;
import java.util.concurrent.Callable;
import java.io.*;
import java.lang.reflect.Array;

public class HOLLightWrapper{

    private BufferedWriter bin;
    private BufferedReader bout;
    private StringBuilder evalStr;
    private Process proc;
private ProcessBuilder interrupt;	
private Boolean holIsEchoing;
private boolean isBuilt;
    private int holPid;

  //variable to keep track of the theorem count
    private int numHolTheorems;

    //variable to hold all the theorems
    private Set<String> holTheorems;

    
private HOLLightWrapper(List<String> command) throws IOException {
	ProcessBuilder pb = new ProcessBuilder(command);
	pb.redirectErrorStream(true);
	evalStr = new StringBuilder();
holIsEchoing = null;
isBuilt = false;
	holPid = 0;
	interrupt = null;
	numHolTheorems = 0;
	holTheorems =  new TreeSet<String>();
	
	    proc =  pb.start();

	
	bin = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream()));
	bout = new BufferedReader(new InputStreamReader(proc.getInputStream()));

    }	
@SuppressWarnings("unchecked")
public Set<String> getTheoremList(){
	return (Set<String>) ((TreeSet<String>) this.holTheorems).clone();
}
protected void setInterrupt(ProcessBuilder kill){
	if (interrupt != null)
		throw new IllegalArgumentException("interrupt already set.");
	else
		interrupt = kill;
}
protected Integer getPID(){
	return holPid;
}
protected void setPID(int pid){
	if (holPid != 0)
		throw new IllegalArgumentException("PID already set.");
	else holPid = pid;
}
protected  void setEcho(boolean b){
	if (holIsEchoing == null)
		holIsEchoing = b;
	else throw new IllegalArgumentException("Already set echo status.");
}
protected  boolean isEchoing(){
	return (holIsEchoing != null) && holIsEchoing;
}
protected void setBuilt() {
	isBuilt = true;
}

protected boolean isBuilt(){
	return isBuilt;
}

    public String getEvalString(){
	String result = evalStr.toString();
	evalStr = new StringBuilder();
	return result;
    }

    public void kill(){
    	proc.destroy();
    }
    
    public void interrupt(){
    	try {
			interrupt.start();
		} catch (IOException e) {
			
			e.printStackTrace();
		}
    }
    

    
    public static Callable<HOLLightWrapper> getHOLBuilderTask(List<String> command) {
    	try {
			return new HOLBuilderTask(new HOLLightWrapper(command));
		} catch (IOException e) {
			
			e.printStackTrace();
		}
		return null;
    }
    


    public boolean isReady() throws IOException{
	return bout.ready();
    }

    public String flushOutput () throws IOException {
	
	    StringBuilder str = new StringBuilder();
	    StringBuilder suppressedOutput = new StringBuilder();
	    char c;
	    do {
		c = (char) bout.read();

		if (str.length() == 0 && c == '@')
		    {
			evalStr.append(bout.readLine());
			evalStr.append(';');
			continue;}
		
		if (c == 65535){
		   
		    suppressedOutput.append(str.toString());
		    //		    print("hol_light: EOF reached.");
		    break;
		}
		str.append(c);		
		
		if (c == 10)
		    {
		
			suppressedOutput.append(str.toString());
			str = new StringBuilder();
			continue;}
		
	    }while (!(
		      str.length() == 2 &&
		      (str.charAt(0) == '#' || str.charAt(0) == ' ') &&
		      str.charAt(1) == ' ' &&
		      !bout.ready()));
	   
	    suppressedOutput.append(str.toString());
	    return suppressedOutput.toString();
	
    }
    
    public String runCommand(String cmd) {
		    
	if(cmd.length() == 0)
	    return null;
	boolean flag = cmd.charAt(cmd.length() - 1) != '\n';
	if(flag)
	    {
		cmd = cmd + "\n";
		//		    printHTML(cmd);
	    }//If we generated the command, dont let them know

	try {
	    bin.write(cmd);
	    bin.flush();

	    //	    conjTac2.setEnabled(true);//Interrupt button	    
	    String result = flushOutput();
	    //if (!flag)
	    //		printHTML(result);
	    //	    conjTac2.setEnabled(false);
	    
	    if(isEchoing()){

	    	
	    	result = result.substring(cmd.length()+1, result.length());
	        }
	    //System.out.println(result);
	    return result;
	    
	} catch (IOException e) {
	    e.printStackTrace();
	    return null;
	}
    }
    
  //method for running multiple hol commands at once
    public void runHOLCommands (String cmds){
	String[] array = cmds.split("\n");

	for(int i = 0; i < Array.getLength(array); i++){
	    runCommand(array[i]);
	}
    }

    
    

  //query hol for the number of theorems in the system  
    private Integer getNumHolTheorems(){
    	String output = runCommand("List.length !theorems;;");
    	//System.out.println(output);
	return parseForInteger(output) ;}

    public static Integer parseForInteger(String rawOutput){
    	int equalsIndex = rawOutput.indexOf('=');
    	rawOutput = rawOutput.substring(equalsIndex + 2);
    	int newlineIndex = rawOutput.indexOf('\n');
    	rawOutput = rawOutput.substring(0,newlineIndex);
    	//System.out.println(rawOutput);
    	return Integer.decode(rawOutput.trim());
    }
    
    public static String parseForString(String rawOutput) throws ParseException{
    	int beginIndex = rawOutput.indexOf('\"') + 1;
	    int endIndex = 0;
    	for (int i = beginIndex;i < rawOutput.length();i++){
	    	if (rawOutput.charAt(i) == '\\'){
	    		i++;
	    		continue;
	    	}
	    	if (rawOutput.charAt(i) == '\"'){
	    		endIndex = i;
	    		break;
	    	}
	    	
	    }
    	if (beginIndex == 0)
    		throw new ParseException("Missing opening \".",0 );
    	if (endIndex == 0)
    		throw new ParseException("Missing closing \".",rawOutput.length()-1);
	    return rawOutput.substring(beginIndex,endIndex);
    }
    
    //method to keep theorem list up to date
    public void updateHolTheorems(){
	if (numHolTheorems != getNumHolTheorems()){
	    numHolTheorems = getNumHolTheorems();
	    	    
	    String bangTheorems = runCommand("String.concat \" \" ((fst o List.split)!theorems);;");
	    String[] bangTheorems2 ;
		try {
			bangTheorems2 = parseForString(bangTheorems).split(" ");
		} catch (ParseException e) {
			
			e.printStackTrace();
			return;
		}
	   
	    for (int i = 0; i < Array.getLength(bangTheorems2); i++){
		    holTheorems.add(bangTheorems2[i]);
	    }
	}
    }
    
}

