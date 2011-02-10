package org.jhol.test;

import org.jhol.core.HOLType;
import org.jhol.core.Term;
import org.jhol.core.lexer.TermParser;
import org.jhol.core.printer.TermPrinter;
import org.jhol.core.printer.TypePrinter;


public class Test {
	public static void main(String[] args) throws Exception {
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
		System.out.println(TermPrinter.simplePrint(term));
		System.out.println(term.makeCamlCommand());
	}
}
