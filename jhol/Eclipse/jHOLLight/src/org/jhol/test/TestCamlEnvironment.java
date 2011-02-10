package org.jhol.test;

import org.jhol.caml.CamlEnvironment;
import org.jhol.caml.CamlObject;
import org.jhol.caml.CamlType;
import org.jhol.core.lexer.TermParser;

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
	public CamlObject execute(String command, CamlType returnType) throws Exception {
		if (!returnType.equals(CamlType.TERM))
			return null;
		
		command = "print_string(raw_string_of_term (" + command + "));;"; 
		String output = caml.runCommand(command);
		output = strip(output);
		
		return TermParser.parseTerm(output);
	}
	
	
	private static String strip(String str) {
		String[] els = str.split("\n");
		return els[0];
		
/*		
		// Find the appropriate element (starting from ")
		String s = null;
		for (String e : els) {
			if (e.trim().startsWith("\"")) {
				s = e;
				break;
			}
		}
		
		if (s == null)
			return str;
		
		str = s.trim();
		if (str.length() < 3)
			return str;
		
		return str.substring(1, str.length() - 2);*/
	}
	
}
