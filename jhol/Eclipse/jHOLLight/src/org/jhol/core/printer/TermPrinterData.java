package org.jhol.core.printer;

import static org.jhol.core.printer.TermPrinter.*;
import static org.jhol.core.Term.*;
import static org.jhol.core.HOLType.*;

import java.math.BigInteger;
import java.util.ArrayList;

import org.jhol.core.HOLType;
import org.jhol.core.Pair;
import org.jhol.core.Term;
import org.jhol.core.printer.TermPrinter.SpecialPrinter;

/**
 * Data for TermPrinter
 */
public class TermPrinterData {
	public static void init() {
		try {
			initInfixes();
			initPrefixes();
			initBinders();
			initInterface();
			initSpecialPrinters();
		}
		catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	/**
	 * initInfixes()
	 */
	public static void initInfixes() {
		parse_as_infix("<=>", 2, InfixAssoc.RIGHT);
		parse_as_infix("==>", 4, InfixAssoc.RIGHT);
		parse_as_infix("\\/", 6, InfixAssoc.RIGHT);
		parse_as_infix("/\\", 8, InfixAssoc.RIGHT);
		parse_as_infix("==", 10, InfixAssoc.RIGHT);
		parse_as_infix("===", 10, InfixAssoc.RIGHT);
		parse_as_infix("treal_eq", 10, InfixAssoc.RIGHT);
		parse_as_infix("IN", 11, InfixAssoc.RIGHT);
		parse_as_infix("belong", 11, InfixAssoc.RIGHT);
		parse_as_infix("--->", 12, InfixAssoc.RIGHT);
		parse_as_infix("-->", 12, InfixAssoc.RIGHT);
		parse_as_infix("<", 12, InfixAssoc.RIGHT);
		parse_as_infix("<<", 12, InfixAssoc.RIGHT);
		parse_as_infix("<<<", 12, InfixAssoc.RIGHT);
		parse_as_infix("<<=", 12, InfixAssoc.RIGHT);
		parse_as_infix("<=", 12, InfixAssoc.RIGHT);
		parse_as_infix("=", 12, InfixAssoc.RIGHT);
		parse_as_infix(">", 12, InfixAssoc.RIGHT);
		parse_as_infix(">=", 12, InfixAssoc.RIGHT);
		parse_as_infix("HAS_SIZE", 12, InfixAssoc.RIGHT);
		parse_as_infix("PSUBSET", 12, InfixAssoc.RIGHT);
		parse_as_infix("SUBSET", 12, InfixAssoc.RIGHT);

		parse_as_infix("+", 16, InfixAssoc.RIGHT);
		parse_as_infix("-", 18, InfixAssoc.LEFT);
		parse_as_infix("*", 20, InfixAssoc.RIGHT);
		parse_as_infix("/", 22, InfixAssoc.RIGHT);
		
	}
	
	
	/**
	 * initPrefixes()
	 */
	public static void initPrefixes() {
		parse_as_prefix("~");
		parse_as_prefix("--");
		parse_as_prefix("mod");
	}
	
	
	/**
	 * initBinders()
	 */
	public static void initBinders() {
		parse_as_binder("\\");
		parse_as_binder("!");
		parse_as_binder("?");
		parse_as_binder("?!");
		parse_as_binder("@");
		parse_as_binder("minimal");
		parse_as_binder("lambda");
		parse_as_binder("lambdas");
	}
	
	
	/**
	 * initInterface()
	 */
	public static void initInterface() throws Exception {
		HOLType real = mk_type("real");
		HOLType num = mk_type("num");
		HOLType bool = mk_type("bool");
		
		HOLType rrr = mk_fun_ty(real, mk_fun_ty(real, real));
		HOLType rrb = mk_fun_ty(real, mk_fun_ty(real, bool));
		HOLType rnr = mk_fun_ty(real, mk_fun_ty(num, real));
		HOLType rr = mk_fun_ty(real, real);
		HOLType nr = mk_fun_ty(num, real);
		
		overload_interface("+", mk_mconst("real_add", rrr));
		overload_interface("-", mk_mconst("real_sub", rrr));
		overload_interface("*", mk_mconst("real_mul", rrr));
		overload_interface("/", mk_mconst("real_div", rrr));
		overload_interface("<", mk_mconst("real_lt", rrb));
		overload_interface("<=", mk_mconst("real_le", rrb));
		overload_interface(">", mk_mconst("real_gt", rrb));
		overload_interface(">=", mk_mconst("real_ge", rrb));
		overload_interface("--", mk_mconst("real_neg", rr));
		overload_interface("pow", mk_mconst("real_pow", rnr));
		overload_interface("inv", mk_mconst("real_inv", rr));
		overload_interface("abs", mk_mconst("real_abs", rr));
		overload_interface("&", mk_mconst("real_of_num", nr));
	}
	
	
	
	public static void initSpecialPrinters() throws Exception {
		HOLType num = mk_type("num");
//		HOLType bool = mk_type("bool");
		HOLType nn = mk_fun_ty(num, num);
		
		
		// EMPTY
		addSpecialPrinter(new SpecialPrinter() {
			@Override
			public boolean test(String s, Term op, ArrayList<Term> args, Term tm) {
				return s.equals("EMPTY") && is_const(tm) && args.size() == 0;
			}
			
			@Override
			public String print(Term tm, Term op, ArrayList<Term> args, int prec) {
				return "{}";
			}
		});
		
		
		// NUMERAL
		final Term numeral = mk_mconst("NUMERAL", nn);

		addSpecialPrinter(new SpecialPrinter() {
			BigInteger r;
			
			@Override
			public boolean test(String s, Term op, ArrayList<Term> args, Term tm) {
				if (op.equals(numeral) && args.size() > 0) {
					Pair<Term,Term> p = dest_comb(tm);
					r = getNumber(p.getSecond());
					return r != null;
				}
				
				return false;
			}
			
			@Override
			public String print(Term tm, Term op, ArrayList<Term> args, int prec) {
				return r.toString();
			}
			
			// Converts a numeral into a number
			BigInteger getNumber(Term t) {
				if (!is_comb(t)) {
					if (is_const(t)) {
						if (dest_const(t).getFirst().equals("_0"))
							return BigInteger.ZERO;
					}
					
					return null;
				}
				
				Pair<Term, Term> p = dest_comb(t);
				Term btm = p.getFirst();
				Term rtm = p.getSecond();
				if (!is_const(btm))
					return null;
				
				BigInteger r = getNumber(rtm);
				if (r == null)
					return null;
				
				String cn = dest_const(btm).getFirst();
				if (cn.equals("BIT0"))
					return r.add(r);
				
				if (cn.equals("BIT1"))
					return r.add(r).add(BigInteger.ONE);
				
				return null;					
			}
		});
	}
}
