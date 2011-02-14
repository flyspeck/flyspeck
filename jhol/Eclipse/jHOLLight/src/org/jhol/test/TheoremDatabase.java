package org.jhol.test;

import java.util.ArrayList;

import org.jhol.caml.CamlEnvironment;
import org.jhol.caml.CamlList;
import org.jhol.caml.CamlObject;
import org.jhol.caml.CamlPair;
import org.jhol.caml.CamlString;
import org.jhol.caml.CamlType;
import org.jhol.core.Term;
import org.jhol.core.Theorem;

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

		for (int i = 0; i < list.size(); i++) {
			CamlPair pair = (CamlPair) list.get(i);
			CamlString name = (CamlString) pair.first();
			Theorem th = (Theorem) pair.second();
			
			result.add(Theorem.mk_theorem(name.str, th.concl()));
		}
		
		return result;
	}
}
