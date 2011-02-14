package org.jhol.test;

import org.jhol.caml.CamlEnvironment;
import org.jhol.caml.CamlObject;
import org.jhol.caml.CamlType;
import org.jhol.core.lexer.Parser;

public class TestCamlEnvironment extends CamlEnvironment {
	private HOLLightWrapper caml;
	
	public TestCamlEnvironment() throws Exception {
		caml = new HOLLightWrapper("hol_light");
		caml.runCommand("needs \"caml/raw_printer.hl\";;");
	}
	
	
	@Override
	public CamlObject execute(String command) throws Exception {
		throw new Exception("Unimplemented");
	}
	
	
	@Override
	public void runCommand(String rawCommand) throws Exception {
		caml.runCommand(rawCommand);
	}
	

	@Override
	public CamlObject execute(String command, CamlType returnType) throws Exception {
		String output;
		
		String printCmd = returnType.getPrintCommand();
		command = "print_string(" + printCmd + "(" + command + "));;";
		System.out.println("Executing: " + command);
		
		output = caml.runCommand(command);
		String testString = output;
		
		if (testString.length() > 1000) {
			testString = testString.substring(0, 1000);
		}
		System.out.println("Out: " + testString);
		
		output = strip(output);
		
		return Parser.parse(output);
		
/*		// Term
		if (returnType.equals(CamlType.TERM)) {
			command = "print_string(raw_string_of_term (" + command + "));;";
			System.out.println("Executing: " + command);
			
			output = caml.runCommand(command);
			System.out.println("Out: " + output);
			
			output = strip(output);
			
			return TermParser.parseTerm(output);
		}
		
		
		// Theorem
		if (returnType.equals(CamlType.THM)) {
			command = "(print_string o raw_string_of_term o concl) (" + command + ");;";
			System.out.println("Executing: " + command);
			
			output = caml.runCommand(command);
			System.out.println("Out: " + output);
			
			output = strip(output);
			
			Term concl = TermParser.parseTerm(output);
			return new Theorem.TempTheorem(concl);
		}

		return null;*/
	}
	
	
	private static String strip(String str) {
		String[] els = str.split("\n");
		
		for (int i = 1; i < els.length; i++) {
			String tmp = els[i].trim();
			if (tmp.startsWith("val it"))
				return els[i - 1];
		}
		
		return els[0];
	}
	
}
