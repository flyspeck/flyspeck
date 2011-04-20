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
		pb.redirectErrorStream(true);
		evalStr = new StringBuilder();

		Process proc;

		proc = pb.start();

		bin = new BufferedWriter(new OutputStreamWriter(proc.getOutputStream()));
		bout = new BufferedReader(new InputStreamReader(proc.getInputStream()));
	}
	

	public boolean isReady() throws IOException {
		return bout.ready();
	}

	public String flushOutput() throws IOException {

		StringBuilder str = new StringBuilder();
		StringBuilder suppressedOutput = new StringBuilder();
		char c;
		do {
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
				if (str.charAt(0) == '#')
					break;
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

}
