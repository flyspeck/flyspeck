//Object for holding hol process
package edu.pitt.math.jhol.test;

import java.util.*;
import java.io.*;

public class HOLLightWrapper {

	private BufferedWriter bin;
	private BufferedReader bout;
	private StringBuilder evalStr;

	public String getEvalString() {
		String result = evalStr.toString();
		evalStr = new StringBuilder();
		return result;
	}
	
	
	public HOLLightWrapper(String ... command) throws IOException {
		ArrayList<String> list = new ArrayList<String>();
		for (String cmd : command)
			list.add(cmd);
		
		init(list);
	}
	

	public HOLLightWrapper(List<String> command) throws IOException {
		init(command);
	}
	
	
	private void init(List<String> command) throws IOException {
		ProcessBuilder pb = new ProcessBuilder(command);
		Map<String, String> env = pb.environment();
		env.put("LD_LIBRARY_PATH", "/usr/local/lib");
		
		pb.redirectErrorStream(true);
		evalStr = new StringBuilder();

		Process proc;
		proc = pb.start();

//		String[] env = {"LD_LIBRARY_PATH=/usr/local/lib"};
//		Process proc = Runtime.getRuntime().exec("cr_restart --no-restore-pid -f /home/monad/hol_light_ckpts/cr_current.cr", env);
		
		bin = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream()));
		bout = new BufferedReader(new InputStreamReader(proc.getInputStream()));
		
//		System.err.println(bout.readLine());
	}
	

	public boolean isReady() throws IOException {
		return bout.ready();
	}

	public String flushOutput() throws IOException {

		StringBuilder str = new StringBuilder();
		StringBuilder suppressedOutput = new StringBuilder();
		char c;
		boolean waitFlag = false;
		
		do {
			if (waitFlag && !bout.ready())
				break;
			
			c = (char) bout.read();

			if (str.length() == 0 && c == '@') {
				evalStr.append(bout.readLine());
				evalStr.append(';');
				continue;
			}

			if (c == 65535) {
				System.err.println("flushOutput: EOF");
				suppressedOutput.append(str.toString());
				// print("hol_light: EOF reached.");
				break;
			}
			str.append(c);

			if (c == 10) {

				suppressedOutput.append(str.toString());
				str = new StringBuilder();
				continue;
			}

	
			if (str.length() == 2) {
				if (str.charAt(0) == '#') {
					if (!bout.ready())
						break;
					
					waitFlag = true;
				}
			}
		}
		while (true);
//		} while (!(str.length() == 2
//				&& (str.charAt(0) == '#' || str.charAt(0) == ' ')
//				&& str.charAt(1) == ' ' && !bout.ready()));

		suppressedOutput.append(str.toString());
		return suppressedOutput.toString();

	}

	public String runCommand(String cmd) {

		if (cmd.length() == 0)
			return null;
		boolean flag = cmd.charAt(cmd.length() - 1) != '\n';
		if (flag) {
			cmd = cmd + "\n";
			// printHTML(cmd);
		}// If we generated the command, dont let them know

		try {
			bin.write(cmd);
			bin.flush();

			// conjTac2.setEnabled(true);//Interrupt button
			String result = flushOutput();
			// if (!flag)
			// printHTML(result);
			// conjTac2.setEnabled(false);

			return result;

		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
	}
	
	
	/**
	 * Test method
	 */
	public static void main(String[] args) {
		try {
//			HOLLightWrapper cmd = new HOLLightWrapper("cr_restart", "--no-restore-pid", "-S", "2",
//					"/home/monad/hol_light_ckpts/cr_current.cr");
			
//			Process proc = Runtime.getRuntime().exec("hol_light");
//			String[] env = {"LD_LIBRARY_PATH=/usr/local/lib"};
//			Process proc = Runtime.getRuntime().exec("cr_restart --no-restore-pid -f /home/monad/hol_light_ckpts/cr_current.cr", env);
			Process proc = Runtime.getRuntime().exec("hol_light2");
			
			BufferedWriter bin = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream()));
			BufferedReader bout = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			BufferedReader berr = new BufferedReader(new InputStreamReader(proc.getErrorStream()));
			
			bin.write("`1 + 1`;;");
			bin.flush();
			
			bin.write("asd;;");
			bin.flush();
			
			System.out.println(berr.readLine());
			System.out.println(bout.readLine());
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}

}
