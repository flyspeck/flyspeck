package edu.pitt.math.jhol.test;


import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.HOLType;
import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.Theorem;

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
	public String runCommand(String rawCommand) throws Exception {
		throw new Exception("Not implemented");
	}
	
}
