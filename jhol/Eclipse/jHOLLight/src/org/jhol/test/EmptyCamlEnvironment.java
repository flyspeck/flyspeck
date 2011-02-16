package org.jhol.test;

import org.jhol.caml.CamlEnvironment;
import org.jhol.caml.CamlObject;
import org.jhol.caml.CamlType;
import org.jhol.core.HOLType;
import org.jhol.core.Term;
import org.jhol.core.Theorem;

/**
 * A Caml environment for test purposes
 * @author Alexey
 *
 */
public class EmptyCamlEnvironment extends CamlEnvironment {
	private final Term testTerm;

	public EmptyCamlEnvironment() {
		testTerm = Term.mk_var("test", HOLType.mk_vartype("Z"));
	}
	
	@Override
	public CamlObject execute(String command) throws Exception {
		throw new Exception("Not implemented");
	}

	@Override
	public CamlObject execute(String command, CamlType returnType)
			throws Exception {
		System.out.println("Executing: " + command);
		
		if (returnType.equals(CamlType.TERM)) {
			return testTerm;
		}
		
		if (returnType.equals(CamlType.THM)) {
			return new Theorem.TempTheorem(testTerm, true);
		}
		
		return null;
	}

	@Override
	public void runCommand(String rawCommand) throws Exception {
		throw new Exception("Not implemented");
	}
	
}
