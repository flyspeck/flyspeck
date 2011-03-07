package edu.pitt.math.jhol;

import java.io.FilterOutputStream;
import java.io.IOException;
import java.io.OutputStream;


//Patch for patch to JConsole
public class UnicodeOutputStream extends FilterOutputStream {

	public UnicodeOutputStream (OutputStream out){
		super (out);
	}
	public void write(byte[] b) throws IOException{
		byte[] tmp = new byte[b.length/6];
		for(int count = 0; count < b.length; count += 6){
		
		
		byte result = 0;
		byte factor = 1;
		for (int i = 5; i >= 2; i--) {
			result += factor * asciiToDecimal(b[count + i]);
			factor *= 16;
		}
		tmp[count/6]=result;
	}
	super.write(tmp);
	}
	
	// begin low level functions
	private static int asciiToDecimal(int c) {
		if (97 <= c) {
			c = c - 87;
		} else {
			c = c - 48;
		}
		return c;
	}

	
}
