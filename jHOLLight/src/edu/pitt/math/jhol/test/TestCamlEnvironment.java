package edu.pitt.math.jhol.test;


import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.parser.Parser;

public class TestCamlEnvironment extends CamlEnvironment {
	private HOLLightWrapper caml;
	
	public TestCamlEnvironment() throws Exception {
		caml = new HOLLightWrapper("hol_light");
		caml.runCommand("needs \"caml/raw_printer.hl\";;");
		caml.runCommand("needs \"caml/ssreflect.hl\";;");
	}
	
	
	@Override
	public CamlObject execute(String command) throws Exception {
		throw new Exception("Unimplemented");
	}
	
	
	@Override
	public void runCommand(String rawCommand) throws Exception {
		System.out.println("Executing: " + rawCommand);
		String output = caml.runCommand(rawCommand);
		System.out.println("Output: " + output);
	}
	

	@Override
	public CamlObject execute(String command, CamlType returnType) throws Exception {
		String output;
		
		String printCmd = returnType.getPrintCommand();
		command = "raw_print_string(" + printCmd + "(" + command + "));;";
		
		command = escape(command);
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
	
	
	private static String escape(String str) {
		StringBuilder out = new StringBuilder(str.length() * 2);
		int n = str.length();
		
		for (int i = 0; i < n; i++) {
			char ch = str.charAt(i);
			if (ch == '\\' && i < n - 1 && str.charAt(i + 1) == '"') {
				out.append('\\');
			}
			
			out.append(ch);
		}
		
		return out.toString();
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
