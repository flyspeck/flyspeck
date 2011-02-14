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
		command = "raw_print_string(" + printCmd + "(" + command + "));;";
		System.out.println("Executing: " + command);
		
		output = caml.runCommand(command);
		String testString = output;
		
		if (testString.length() > 1000) {
			testString = testString.substring(0, 1000);
		}
		System.out.println("Out: " + testString);
		
		output = strip(output);
		if (output == null) {
			System.err.println("Null result");
			return null;
		}
		
		return Parser.parse(output);
	}
	
	
	private static String strip(String str) {
		int i1 = str.indexOf("$begin$");
		int i2 = str.indexOf("$end$");
		
		if (i2 <= i1)
			return null;
		
		return str.substring(i1 + "$begin".length() + 1, i2);
		
		
/*		String[] els = str.split("\n");
		
		for (int i = 1; i < els.length; i++) {
			String tmp = els[i].trim();
			if (tmp.startsWith("val it"))
				return els[i - 1];
		}
		
		return els[0];*/
	}
	
}
