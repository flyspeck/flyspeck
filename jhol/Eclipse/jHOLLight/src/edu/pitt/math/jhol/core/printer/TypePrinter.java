package edu.pitt.math.jhol.core.printer;

import edu.pitt.math.jhol.core.HOLType;
import edu.pitt.math.jhol.core.Pair;

/**
 * Contains functions for printing HOL Types
 */
public class TypePrinter {
	/**
	 * Converts a HOL Type into a string
	 */
	public static String printType(HOLType type) {
		return printType(type, 0);
	}
	
	
	/**
	 * Special version of the printType() function with priority
	 */
	protected static String printType(HOLType type, int priority) {
		Pair<String, HOLType[]> pair = type.dest();
		String name = pair.getFirst();
		HOLType[] args = pair.getSecond();
		
		if (args == null) {
			// TyVar
			return name;
		}
		else {
			// TyApp
			if (args.length == 0)
				return name;
			
			if (name.equals("fun"))
				return printType("->", priority > 0, printType(args[0], 1), printType(args[1], 0));
			
			if (name.equals("sum"))
				return printType("+", priority > 2, printType(args[0], 3), printType(args[1], 2));
			
			if (name.equals("prod"))
				return printType("#", priority > 4, printType(args[0], 5), printType(args[1], 4));
			
			if (name.equals("cart"))
				return printType("^", priority > 6, printType(args[0], 6), printType(args[1], 7));

			String[] ss = new String[args.length];
			for (int i = 0; i < args.length; i++)
				ss[i] = printType(args[i], 0);
			
			String str = printType(",", true, ss);
			return str + name;
		}
	}
	
	
	/**
	 * Auxiliary function
	 */
	protected static String printType(String sep, boolean flag, String ... ss) {
		if (ss.length == 0)
			return "";
		
		StringBuilder str = new StringBuilder();
		if (flag)
			str.append('(');
		
		int n = ss.length;
		for (int i = 0; i < n; i++) {
			str.append(ss[i]);
			if (i < n - 1)
				str.append(sep);
		}
		
		if (flag)
			str.append(')');
		
		return str.toString();
	}
}
