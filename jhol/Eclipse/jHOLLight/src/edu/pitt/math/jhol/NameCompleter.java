package edu.pitt.math.jhol;

import java.lang.reflect.Array;

import bsh.util.NameCompletion;

public class NameCompleter implements NameCompletion {
	private TheoremCompletor holTheoremCompletor;
	public NameCompleter (TheoremCompletor holTheoremCompletor){
		this.holTheoremCompletor = holTheoremCompletor;
	}
	public String[] completeName (String part){
	    int matches = 0;
	    int[] index = new int[11];
	    int len = part.length();
	    int current = 0;
	    
	    while (matches < 11 && current < Database.NUM_HOL_COMMANDS){
		if (part.regionMatches(false,0,Database.HOL_COMMANDS_STRING[current],0,len)){
		    index[matches] = current;
		    matches++;}
		current++;
	    }
	    String[] thms = null;
	    int thmlen = 0;
	    if (matches < 11)
		{
		    thms = holTheoremCompletor.completeName(part);
		    if (thms != null)
			thmlen = Array.getLength(thms);
		}
	    if (thmlen + matches > 11)
		thmlen = 11 - matches;
	    String[] result = new String[matches + thmlen];
	    int i;
	    for (i = 0; i < matches; i++){
		result[i] = Database.HOL_COMMANDS_STRING[index[i]];
	    }
	    for (int j = 0; i < matches + thmlen; i++){
		result[i]  = thms[j];
		j++;
	    }

	    //Return max common
	    int shortResultLength = result[0].length();
	    for ( i = 1; i < matches + thmlen; i++){
		if (result[i].length() < shortResultLength)
		    shortResultLength = result[i].length();}
	    //This finds the shortest name
	    
	    if (thmlen + matches < 11 && thmlen + matches > 1 && part.length() < shortResultLength){
		int resultLength;
		String[] tmpresult;
		for (resultLength = part.length(); resultLength < shortResultLength; resultLength++){
		    char testChar = result[0].charAt(resultLength);
		    for ( i = 0; i < matches + thmlen; i ++){
			if (testChar != result[i].charAt(resultLength) && resultLength == part.length()){
			    return result;
			}
			if (testChar != result[i].charAt(resultLength)){
			    tmpresult = new String[1];
			    tmpresult[0] = result[0].substring(0,resultLength);
			    return tmpresult;}

		    }
		}
		tmpresult = new String[1];
		tmpresult[0] = result[0];
		return tmpresult;
	    }
	
	    return result;
	}
}
