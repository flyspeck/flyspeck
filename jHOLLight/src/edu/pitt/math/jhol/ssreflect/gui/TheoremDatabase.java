package edu.pitt.math.jhol.ssreflect.gui;

import java.util.ArrayList;

import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlList;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlPair;
import edu.pitt.math.jhol.caml.CamlString;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.Theorem;
import edu.pitt.math.jhol.core.parser.Parser;

/**
 * A database of theorems
 */
public class TheoremDatabase {
	private final CamlEnvironment caml;
	
	/**
	 * Constructor
	 */
	public TheoremDatabase(CamlEnvironment env) {
		this.caml = env;
	}
	
	
	/**
	 * Finds all theorems containing the given term t
	 */
	public ArrayList<Theorem> find(Term t) {
		ArrayList<Theorem> result = new ArrayList<Theorem>();
		
		// Prepare a command
		String tCmd = t.makeCamlCommand();
		String cmd = "search[" + tCmd + "]";
		
		CamlType pairType = new CamlType.PairType(CamlType.STRING, CamlType.THM);
		CamlType returnType = new CamlType.ListType(pairType);
		
		// Execute the command
		CamlObject obj;
		try {
			obj = caml.execute(cmd, returnType);
		}
		catch (Exception e) {
			e.printStackTrace();
			return result;
		}
		
		// Process the result
		CamlList list = (CamlList) obj;
		if (list == null)
			return result;

		for (int i = 0; i < list.size(); i++) {
			CamlPair pair = (CamlPair) list.get(i);
			CamlString name = (CamlString) pair.first();
			Theorem th = (Theorem) pair.second();
			
			result.add(Theorem.mk_theorem(name.str, th.concl()));
		}
		
		return result;
	}
	
	
	/**
	 * Finds all theorems using the string of mixed names and terms
	 */
	public ArrayList<Theorem> find(String str) {
		ArrayList<Theorem> result = new ArrayList<Theorem>();

		if (str == null)
			return result;

		// Prepare the search command
		StringBuffer cmd = new StringBuffer("search [");

		int index = 0;
		boolean firstFlag = true;
		
		while (true) {
			// Get name
			int i = str.indexOf('`', index);
			String name = null;
			
			if (i < 0)
				name = str.substring(index).trim();
			else if (i > index)
				name = str.substring(index, i).trim();
			
			if (name != null && name.length() > 0) {
				// The names could be separated by a space
				String[] names = name.split(" ");
				for (String name0 : names) {
					if (name0 == null || name0.length() == 0)
						continue;
					
					if (!firstFlag)
						cmd.append("; ");
					cmd.append("name \"" + name0 + '"');
					
					firstFlag = false;
				}
			}
			
			if (i < 0)
				break;
			
			index = i + 1; 
			
			// Get term
			i = str.indexOf('`', index);
			String term = null;
			
			if (i < 0)
				term = str.substring(index);
			else if (i > index)
				term = str.substring(index, i);
			
			if (term != null && term.length() > 0) {
				if (!firstFlag)
					cmd.append("; ");
				cmd.append("`" + term + "`");
				firstFlag = false;
			}
			
			if (i < 0)
				break;
			
			index = i + 1;
		}
		
		cmd.append("]");
		
		// Execute the command
		CamlType pairType = new CamlType.PairType(CamlType.STRING, CamlType.THM);
		CamlType returnType = new CamlType.ListType(pairType);
		CamlObject obj;

		try {
			obj = caml.execute(cmd.toString(), returnType);
		}
		catch (Exception e) {
			e.printStackTrace();
			return result;
		}
		
		// Process the result
		CamlList list = (CamlList) obj;
		if (list == null)
			return result;

		for (int i = 0; i < list.size(); i++) {
			CamlPair pair = (CamlPair) list.get(i);
			CamlString name = (CamlString) pair.first();
			Theorem th = (Theorem) pair.second();
			
			result.add(Theorem.mk_theorem(name.str, th.concl()));
		}
		
		return result;
	}
	
	
	/**
	 * Parses the given string containing theorems and their names
	 */
	public ArrayList<Theorem> parse(String str) {
		ArrayList<Theorem> result = new ArrayList<Theorem>();
		CamlList list = null;
		
		try {
			list = (CamlList) Parser.parse(str);
		}
		catch (Exception e) {
			e.printStackTrace();
		}
		
		if (list == null)
			return result;

		for (int i = 0; i < list.size(); i++) {
			CamlPair pair = (CamlPair) list.get(i);
			CamlString name = (CamlString) pair.first();
			Theorem th = (Theorem) pair.second();
			
			result.add(Theorem.mk_theorem(name.str, th.concl()));
		}
		
		return result;
	}
}
