package edu.pitt.math.jhol.test;


import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.parser.Parser;

public class TestCamlEnvironment extends CamlEnvironment {
	private HOLLightWrapper caml;
	private String output;
	
	public TestCamlEnvironment(String holName) throws Exception {
		caml = new HOLLightWrapper(holName);
//		caml = new HOLLightWrapper("dmtcp_restart", "/home/monad/hol_light_ckpts/cp4_trig_hyp_fan_pack_tame.dmtcp");
//		caml = new HOLLightWrapper("cr_restart", "--no-restore-pid", "-S", "2", 
//					"/home/monad/hol_light_ckpts/cr_current.cr");
		caml.runCommand("needs \"caml/raw_printer.hl\";;");
		caml.runCommand("needs \"caml/ssreflect.hl\";;");
		caml.runCommand("needs \"caml/sections.hl\";;");
	}
	
	
	@Override
	public CamlObject execute(String command) throws Exception {
		throw new Exception("Unimplemented");
	}
	
	
	@Override
	public String runCommand(String rawCommand) throws Exception {
		System.out.println("Executing: " + rawCommand);
		output = caml.runCommand(rawCommand);
		System.out.println("Output: " + output);
		
		return output;
	}
	

	@Override
	public CamlObject execute(String command, CamlType returnType) throws Exception {
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
		
		String result = strip(output);
		if (result == null) {
			System.err.println("Null result");
			return null;
		}
		
		return Parser.parse(result);
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
	}


	@Override
	public String getRawOutput() {
		return output;
	}
	
}
