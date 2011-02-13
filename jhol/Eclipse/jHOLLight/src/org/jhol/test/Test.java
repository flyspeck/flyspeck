package org.jhol.test;

import java.io.BufferedReader;

import java.io.InputStreamReader;
import java.util.ArrayList;

import org.jhol.core.HOLType;
import org.jhol.core.Pair;
import org.jhol.core.Term;
import org.jhol.core.lexer.TermParser;
import org.jhol.core.printer.TermPrinter;
import org.jhol.core.printer.TypePrinter;

import static org.jhol.core.HOLType.*;
import static org.jhol.core.Term.*;


public class Test {
	public static void test1() throws Exception {
		String test = "Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"hull\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])])])])),Const(\"convex\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])]))),Const(\"EMPTY\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])])))),Const(\"EMPTY\",Tyapp(\"fun\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyvar(\"?221889\")]),Tyapp(\"bool\"[])])))";
		test = "Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Comb(Comb(Const(\"=\",Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"fun\"[Tyapp(\"bool\"[]),Tyapp(\"bool\"[])])])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyvar(\"A\")),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyvar(\"B\")),Comb(Comb(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Var(\"x\",Tyvar(\"A\"))),Var(\"y\",Tyvar(\"B\")))))))),Comb(Const(\"?\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")]),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"y\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")])),Comb(Const(\"!\",Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"bool\"[])]),Tyapp(\"bool\"[])])),Abs(Var(\"x\",Tyvar(\"A\")),Comb(Comb(Var(\"P\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyapp(\"fun\"[Tyvar(\"B\"),Tyapp(\"bool\"[])])])),Var(\"x\",Tyvar(\"A\"))),Comb(Var(\"y\",Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")])),Var(\"x\",Tyvar(\"A\")))))))))))";
		test = "Comb(Comb(Var(\"f\",Tyapp(\"fun\"[Tyvar(\"?961032\"),Tyapp(\"fun\"[Tyvar(\"?961031\"),Tyvar(\"?961030\")])])),Comb(Var(\"g\",Tyapp(\"fun\"[Tyvar(\"?961033\"),Tyvar(\"?961032\")])),Var(\"x\",Tyvar(\"?961033\")))),Var(\"y\",Tyvar(\"?961031\")))";
		String testType = "Tyapp(\"fun\"[Tyapp(\"fun\"[Tyvar(\"A\"),Tyvar(\"B\")]),Tyapp(\"prod\"[Tyapp(\"cart\"[Tyapp(\"real\"[]),Tyapp(\"real\"[])]),Tyapp(\"1\"[])])])";
		
		// Type test
		System.out.println("TYPE");
		HOLType type = TermParser.parseType(testType);
		
		System.out.println("type = " + type);
		System.out.println(TypePrinter.printType(type));
		
		System.out.println(type.makeCamlCommand());

		// Term test
		System.out.println("TERM");
		Term term = TermParser.parseTerm(test);
		
		System.out.println("term = " + term);
		System.out.println(TermPrinter.print(term));
		System.out.println(term.makeCamlCommand());
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
	
	
	/**
	 * test2
	 * @throws Exception
	 */
	public static void test2() throws Exception {
		HOLLightWrapper console = new HOLLightWrapper("hol_light");
		console.runCommand("needs \"caml/raw_printer.hl\";;");

		BufferedReader br = new BufferedReader(new InputStreamReader(System.in));

		while (true) {
			String command = br.readLine();
			if (command == null || command.equals("exit"))
				break;
			
			String output = console.runCommand(command);
			
			output = strip(output);
			
			System.out.println(output);
		}
		
	}
	
	static HOLType num;
	static HOLType bool;
	static HOLType aty;
	static HOLType bty;
	
	static {
		try {
			num = mk_type("num");
			bool = mk_type("bool");
			aty = mk_vartype("A");
			bty = mk_vartype("B");
		}
		catch (Exception e) {
		}
	}
	
	/**
	 * test3
	 */
	public static void test3() throws Exception {
		
		HOLType t1 = mk_fun_ty(aty, mk_fun_ty(bty, bool));
		HOLType t2 = mk_fun_ty(num, mk_fun_ty(bool, bool));
		
		ArrayList<Pair<HOLType,HOLType>> t = t1.type_match(t2, null); 

		String str = "";
		if (t != null) {
			str += "[";
			for (int i = 0; i < t.size(); i++) {
				str += TypePrinter.printType(t.get(i).getFirst());
				str += ", ";
				str += TypePrinter.printType(t.get(i).getSecond());
				str += "; ";
			}
			
			str += "]";
		}
		
		System.out.println(str);
	}
	
	
	public static void test(Pair<Term, ArrayList<Term>> p) {
		String str = "(";
		str += TermPrinter.print(p.getFirst());
		str += ", ";
		str += "[";
		
		for (Term x : p.getSecond()) {
			str += TermPrinter.print(x);
			str += "; ";
		}
		str += "])";

		System.out.println(str);
	}
	
	/**
	 * test4
	 */
	public static void test4() throws Exception {
		Term f = mk_var("f", mk_fun_ty(num, mk_fun_ty(bool, aty)));
		Term t1 = mk_var("t1", num);
		Term t2 = mk_var("t2", bool);
		
		Term t = mk_comb(mk_comb(f, t1), t2);
		
		System.out.println(TermPrinter.print(t));
		
		test(strip_comb(t));
		test(strip_comb(t1));
		test(strip_comb(f));
	}
	
	
	/**
	 * main
	 * @param args
	 * @throws Exception
	 */
	public static void main(String[] args) throws Exception {
		test4();
		
		System.exit(0);
	}
}
