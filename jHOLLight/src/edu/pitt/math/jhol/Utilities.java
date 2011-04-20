package edu.pitt.math.jhol;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;

public class Utilities {
	

	public static String readFile(String filename){
	    String result = null;
	    BufferedReader stream = null;
		try{
		//print(filename);
		File file = new File(filename);
		// print(file);
		stream = new BufferedReader(new FileReader(file));
		int c = stream.read();
		StringBuilder sb = new StringBuilder();
		while (c != -1){
		    sb.append((char)c);
		    c = stream.read();
		}
		result = sb.toString();

	    }
	    catch (IOException x) {
		System.err.println(x);
	    } 
	    finally{
		if (stream != null)
			try {
				stream.close();
			} catch (IOException e) {
				
				e.printStackTrace();
			}
	    }
	    return result;
	}

	void appendStringToFilename(String s, String p){
	    //Convert the string to a byte array.
	    byte[] data = s.getBytes();
	    
	    OutputStream out = null;
	    try {
		out = new BufferedOutputStream(new FileOutputStream(p));
		out.write(data, 0, data.length);
	    } catch (IOException x) {
		System.err.println(x);
	    } finally {
		if (out != null) {
		    try {
				out.flush();
				out.close();
			} catch (IOException e) {
				
				e.printStackTrace();
			}
		    
		}
	    }
	}

	
	//end low level functions

}
