package edu.pitt.math.jhol;

import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.OutputStream;

public class Utilities {
	//begin low level functions
	public static int asciiToDecimal(int c){
	    if (97 <= c){
		c = c - 87;}else{
		c = c - 48;}
	    return  c;}

	public static int getChar(BufferedReader br){
	    char[] tmp = new char[6];
	    for (int i = 0; i < 6; i++)
			try {
				tmp[i] = (char)br.read();
			} catch (IOException e) {
				
				e.printStackTrace();
			}
	    int result = 0;
	    int factor = 1;
	    for (int i = 5; i >= 2; i--){
		result += factor * asciiToDecimal(tmp[i]);
		factor *= 16;}
	    return  result;}

	public static String readLine(BufferedReader br){
	    StringBuilder sb = new StringBuilder();
	    while(true){
		int c = getChar(br);
		if(c==10)
		    break;
	        sb.appendCodePoint(c);
	    }
	    return sb.toString();
	}

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
