package edu.pitt.math.jhol;

import java.text.ParseException;
import java.util.LinkedList;
import java.util.List;

import edu.pitt.math.jhol.core.parser.HOLLightWrapper;



import bsh.util.NameCompletion;

public class TheoremCompletor implements NameCompletion{
	private HOLLightWrapper hol;
	public TheoremCompletor (HOLLightWrapper hol){
		this.hol = hol;
	}
	
		public String[] completeName(String part){
		    try {
				hol.updateHolTheorems();
			} catch (ParseException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		    List<String> preResult = new LinkedList<String> ();
		    for (String s : hol.getTheoremList()){
			if (s.startsWith(part)){
			    preResult.add(s);
			}
		    }
		    int numResult = preResult.size() > 11 ? 11 : preResult.size();
		    String[] result = new String[numResult];	    
		    int i = 0;
		    for(String s : preResult){
			result[i] = s;
			i++;
			if (i == numResult)
			    break;
		    }
		    return result;
		}
	   
}
