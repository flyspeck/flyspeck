package edu.pitt.math.jhol.core.printer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import edu.pitt.math.jhol.core.HOLType;
import edu.pitt.math.jhol.core.Pair;
import edu.pitt.math.jhol.core.Term;
import static edu.pitt.math.jhol.core.Term.*;
import static edu.pitt.math.jhol.core.TermUtils.*;

/**
 * Prints a term
 */
public class TermPrinter {
	// Associativity values of infix operations
	public static enum InfixAssoc {
		LEFT,
		RIGHT
	}
	
	// The set of binders
	private static final HashSet<String> binders;
	
	// Describes an overloaded interface
	private static class Interface {
		public final String id;
		public final String name;
		public final HOLType type;
		
		public Interface(String id, String name, HOLType type) {
			this.id = id;
			this.name = name;
			this.type = type;
		}
	}
	
	// The list of interface mappings
	private static final ArrayList<Interface> the_interface;
	
	// The list of the infixes
	private static final HashMap<String, Pair<Integer, InfixAssoc>> infixes;
	
	// The set of the prefixes
	private static final HashSet<String> prefixes;
	
	// The set of binary operators that print without surrounding spaces
	private static final HashSet<String> unspaced_binops;
	
	// Flag determining whether interface is reversed on printing
	private static boolean reverse_interface_mapping = true;	
	
	

	// Special printers
	public static ArrayList<SpecialPrinter> specialPrinters;
	
	// For printing special terms (NUMERAL, GABS, etc.)
	public static abstract class SpecialPrinter {
		public SpecialPrinter() {
		}
		
		public abstract TermPrinterTree print(Term tm, String s, Term op, ArrayList<Term> args, int prec);
	}
	
	
	// Static initialization
	static {
		binders = new HashSet<String>();
		the_interface = new ArrayList<Interface>();
		infixes = new HashMap<String, Pair<Integer,InfixAssoc>>();
		prefixes = new HashSet<String>();
		unspaced_binops = new HashSet<String>();
		
		specialPrinters = new ArrayList<SpecialPrinter>();
	}
	
	

	/**
	 * Adds a special printer
	 */
	public static void addSpecialPrinter(SpecialPrinter printer) {
		specialPrinters.add(printer);
	}
	
	
	
	/**
	 * Sets the reverse_interface_mapping flag
	 */
	public static void setReverseInterfaceMapping(boolean flag) {
		reverse_interface_mapping = flag;
	}
	
	
	/**
	 * Adds the binary operator to the set of unspaced binary operators
	 */
	public static void addUnspacedBinop(String op) {
		unspaced_binops.add(op);
	}
	
	
	/**
	 * Adds an identifier to the set of binders
	 */
	public static void parse_as_binder(String str) {
		binders.add(str);
	}
	
	
	/**
	 * Returns true if the given string has binder status
	 */
	public static boolean parses_as_binder(String str) {
		return binders.contains(str);
	}
	
	
	/**
	 * Adds the identifier to the list of infixes
	 */
	public static void parse_as_infix(String id, int prec, InfixAssoc assoc) {
		infixes.put(id, new Pair<Integer,InfixAssoc>(prec, assoc));
	}
	
	
	/**
	 * Adds the identifier to the list of prefixes
	 */
	public static void parse_as_prefix(String id) {
		prefixes.add(id);
	}
	
	
	/**
	 * Returns true if the identifier is a prefix
	 */
	public static boolean is_prefix(String id) {
		return prefixes.contains(id);
	}
	
	
	/**
	 * Gets the precedence and associativity of the infix operator
	 */
	public static Pair<Integer,InfixAssoc> get_infix_status(String op) {
		return infixes.get(op);
	}
	
	
	/**
	 * Overloads the symbol
	 * @param str
	 * @param tm must be a variable or constant
	 */
	public static void overload_interface(String str, Term tm) {
		if (!is_var(tm) && !is_const(tm))
			return;
		
		Pair<String,HOLType> p;
		
		if (is_var(tm))
			p = dest_var(tm);
		else
			p = dest_const(tm);
		
		the_interface.add(new Interface(str, p.getFirst(), p.getSecond()));
	}
	
	

	
	
	/**
	 * Converts the given term into a string
	 */
	public static TermPrinterTree print(Term t) {
//		return printSimple(t);
		return print_term(t, 0);
	}
	
	
	/**
	 * Prints a term without any special rules
	 */
	public static String printSimple(Term t) {
		if (is_var(t)) {
			Pair<String, HOLType> p = dest_var(t);
			return p.getFirst();
		}
		
		if (is_const(t)) {
			Pair<String, HOLType> p = dest_const(t);
			return "(" + p.getFirst() + ")";
		}
		
		if (is_comb(t)) {
			Pair<Term, Term> p = dest_comb(t);
			Term t1 = p.getFirst();
			Term t2 = p.getSecond();
			
			String s1 = printSimple(p.getFirst());
			String s2 = printSimple(p.getSecond());
			
			if (is_abs(t1))
				s1 = "(" + s1 + ")";
			
			if (is_comb(t2) || is_abs(t2))
				s2 = "(" + s2 + ")";
			
			return s1 + " " + s2;
		}
		
		if (is_abs(t)) {
			Pair<Term, Term> p = dest_abs(t);
			String s1 = printSimple(p.getFirst());
			String s2 = printSimple(p.getSecond());
			
			return "\\" + s1 + ". " + s2;
		}
		
		throw new Error("Impossible");
	}
	
	
	/**
	 * Returns the name of a constant or variable
	 */
	static String name_of(Term tm) {
		if (is_var(tm))
			return dest_var(tm).getFirst();
		
		if (is_const(tm))
			return dest_const(tm).getFirst();
		
		return "";
	}
	
	
	/**
	 * Finds an identifier corresponding to the given interface
	 */
	static String reverse_interface(String s0, HOLType ty0) {
		if (!reverse_interface_mapping)
			return s0;
		
		for (Interface i : the_interface) {
			if (!s0.equals(i.name))
				continue;

			if (i.type.type_match(ty0, null) == null)
				continue;
			
			return i.id;
		}
		
		return s0;
	}
	
	static String reverse_interface(Pair<String, HOLType> p) {
		return reverse_interface(p.getFirst(), p.getSecond());
	}
	
	
	/**
	 * Prints a list of terms
	 */
	static TermPrinterTree print_term_sequence(TermPrinterTree node, String sep, int prec, ArrayList<Term> tms) {
		int n = tms.size();
		for (int i = 0; i < n; i++) {
			Term tm = tms.get(i);
			
			TermPrinterTree branch = print_term(tm, prec);
			node.addBranch(branch);

			if (i < n - 1)
				node.addBranch(new TermPrinterTree(null, sep));
		}
		
		return node;
	}
	
	
	/**
	 * Special dest_binary function
	 */
	private static Pair<Term, Term> dest_binary(Term op, Term tm) {
		if (!is_comb(tm))
			return null;
		
		Pair<Term,Term> p = dest_comb(tm);
		Term il = p.getFirst();
		Term r = p.getSecond();
		
		if (!is_comb(il))
			return null;
		
		p = dest_comb(il);
		Term i = p.getFirst();
		Term l = p.getSecond();
		
		if (i.equals(op) || (is_const(i) && is_const(op) && 
				reverse_interface(dest_const(i)).equals(reverse_interface(dest_const(op))))) {
			return new Pair<Term,Term>(l, r);
		}
		
		return null;
	}
	
	
	/**
	 * Prints a binder
	 */
	static TermPrinterTree print_binder(final Term tm, final int prec) {
		boolean absf = is_gabs(tm);
		
		String s = absf ? "\\" : name_of(rator(tm));
		// Collect the bounded variables
		Pair<ArrayList<Pair<Boolean, Term>>, Term> vs_bod = collectvs(absf, s, tm);
		ArrayList<Pair<Boolean, Term>> vs = vs_bod.getFirst();
		Term bod = vs_bod.getSecond();

		TermPrinterTree node = new TermPrinterTree(tm, s);
		
		if (prec != 0)
			node.setBrackets("(", ")");
		
//		if (isalnum(s))
//			str.append(' ');
		char ch = s.length() > 0 ? s.charAt(0) : 0;
		if (Character.isDigit(ch) || Character.isLetter(ch) || ch == '_' || ch == '\'')
			node.addBranch(new TermPrinterTree(null, " "));
		
		for (int i = 0; i < vs.size(); i++) {
			Pair<Boolean, Term> p = vs.get(i);
			TermPrinterTree branch = print_term(p.getSecond(), 0);
			
			if (p.getFirst())
				branch.setBrackets("(", ")");

			node.addBranch(branch);
			
			if (i < vs.size() - 1)
				node.addBranch(new TermPrinterTree(null, " "));
			else
				node.addBranch(new TermPrinterTree(null, "."));
		}

		node.addBranch(new TermPrinterTree(null, " "));
		
		TermPrinterTree body = print_term(bod, 0);
		node.addBranch(body);
		
		return node;
	}
	
	
	
	/**
	 * Auxiliary function for collecting bounded variables
	 */
	private static Pair<ArrayList<Pair<Boolean, Term>>, Term> collectvs(boolean absf, String s, Term tm) {
//		ArrayList<Pair<Boolean, Term>> vars = new ArrayList<Pair<Boolean,Term>>();
		
		if (absf) {
			// Generalized abstraction
			if (is_abs(tm)) {
				Pair<Term, Term> p = dest_abs(tm);
				Term v = p.getFirst();
				Term t = p.getSecond();
				
				Pair<ArrayList<Pair<Boolean, Term>>, Term> vs_bod = collectvs(absf, s, t);
				vs_bod.getFirst().add(0, new Pair<Boolean, Term>(false, v));
				return vs_bod;
			}
			else if (is_gabs(tm)) {
				Pair<Term, Term> p = dest_gabs(tm);
				Term v = p.getFirst();
				Term t = p.getSecond();
				
				Pair<ArrayList<Pair<Boolean, Term>>, Term> vs_bod = collectvs(absf, s, t);
				vs_bod.getFirst().add(0, new Pair<Boolean, Term>(true, v));
				return vs_bod;
			}
			
			ArrayList<Pair<Boolean, Term>> vars = new ArrayList<Pair<Boolean,Term>>();
			return new Pair<ArrayList<Pair<Boolean,Term>>, Term>(vars, tm);
		}
		
		// Binder
		if (is_comb(tm) && name_of(rator(tm)).equals(s)) {
			if (is_abs(rand(tm))) {
				Pair<Term, Term> p = dest_abs(rand(tm));
				Term v = p.getFirst();
				Term t = p.getSecond();
				
				Pair<ArrayList<Pair<Boolean, Term>>, Term> vs_bod = collectvs(absf, s, t);
				vs_bod.getFirst().add(0, new Pair<Boolean, Term>(false, v));
				return vs_bod;
			}
			else if (is_gabs(rand(tm))) {
				Pair<Term, Term> p = dest_gabs(rand(tm));
				Term v = p.getFirst();
				Term t = p.getSecond();
				
				Pair<ArrayList<Pair<Boolean, Term>>, Term> vs_bod = collectvs(absf, s, t);
				vs_bod.getFirst().add(0, new Pair<Boolean, Term>(true, v));
				return vs_bod;
			}
		}
		
		ArrayList<Pair<Boolean, Term>> vars = new ArrayList<Pair<Boolean,Term>>();
		return new Pair<ArrayList<Pair<Boolean,Term>>, Term>(vars, tm);
	}
	
	
	/**
	 * Prints the given term with the given precedence
	 * @param tm
	 * @param prec
	 * @return
	 */
	public static TermPrinterTree print_term(final Term tm, final int prec) {
		if (is_gabs(tm))
			return print_binder(tm, prec);
		
		// Split an operation and its arguments
		Pair<Term, ArrayList<Term>> op_args = strip_comb(tm);
		Term hop = op_args.getFirst();
		ArrayList<Term> args = op_args.getSecond();
		int nargs = args.size();
		
		String s0 = name_of(hop);
		HOLType ty0 = hop.type(); 
		
		// Find the inverse interface
		String s = reverse_interface(s0, ty0);
		
		
		//////////////////////////////
		// Test special printers
		
		for (SpecialPrinter printer : specialPrinters) {
			TermPrinterTree test = printer.print(tm, s, hop, args, prec);
			if (test != null)
				return test;
		}
		

		TermPrinterTree node = new TermPrinterTree(tm, null);
		TermPrinterTree opNode = new TermPrinterTree(hop, s);
		TermPrinterTree spaceNode = new TermPrinterTree(null, " ");
		
		//////////////////////////////
		
		// Prefix operations
		if (prefixes.contains(s) && nargs == 1) {
			if (prec == 1000)
				node.setBrackets("(", ")");

			TermPrinterTree spacedOp = new TermPrinterTree(hop, " " + s);
//			node.addBranch(opNode);
			node.addBranch(spacedOp);
			
			// Forced space
//			node.addBranch(spaceNode);

			TermPrinterTree argNode = print_term(args.get(0), 999);
			node.addBranch(argNode);
			
			return node;
		}
		
		////////////////////////////////
		
		// Binders
		if (parses_as_binder(s) && nargs == 1 && is_gabs(args.get(0))) {
			return print_binder(tm, prec);
		}
		
		///////////////////////////////
		
		// Infix operations
		Pair<Integer,InfixAssoc> infix = get_infix_status(s);
		if (infix != null && nargs == 2) {
			ArrayList<Term> bargs = new ArrayList<Term>();
			
			if (infix.getSecond() == InfixAssoc.RIGHT) {
				// Right associativity
				// Break apart the binary operation(s)
				Term tmp = tm;
				while (true) {
					Pair<Term,Term> p = dest_binary(hop, tmp);
					if (p == null) {
						bargs.add(tmp);
						break;
					}
					
					bargs.add(p.getFirst());
					tmp = p.getSecond();
				}
			}
			else {
				// Left associativity
				// Break apart the binary operation(s)
				Term tmp = tm;
				while (true) {
					Pair<Term,Term> p = dest_binary(hop, tmp);
					if (p == null) {
						bargs.add(0, tmp);
						break;
					}
					
					bargs.add(0, p.getSecond());
					tmp = p.getFirst();
				}
			}
			
			int newprec = infix.getFirst();
			if (newprec <= prec)
				node.setBrackets("(", ")");
			
			boolean unspaced = unspaced_binops.contains(s);
			TermPrinterTree spacedOp = opNode;
			if (!unspaced)
				spacedOp = new TermPrinterTree(hop, " " + s + " ");
			
			int nbargs = bargs.size();
			for (int i = 0; i < nbargs; i++) {
				TermPrinterTree argNode = print_term(bargs.get(i), newprec);
				node.addBranch(argNode);

				if (i < nbargs - 1) {
					// Print the operation
					node.addBranch(spacedOp);
/*					if (!unspaced)
						node.addBranch(spaceNode);

					node.addBranch(opNode);
					
					if (!unspaced)
						node.addBranch(spaceNode);*/
				}
			}
			
			return node;
		}
	
		
		// Constants and variables
		if ((is_const(hop) || is_var(hop)) && nargs == 0) {
			node = opNode;
			
			if (parses_as_binder(s) || get_infix_status(s) != null || is_prefix(s)) {
				node.setBrackets("(", ")");
			}
			
			return node;
		}

		// Combinations
		Pair<Term,Term> p = dest_comb(tm);
		Term l = p.getFirst();
		Term r = p.getSecond();
		
		if (prec == 1000)
			node.setBrackets("(", ")");
		
		TermPrinterTree lNode = print_term(l, 999);
		node.addBranch(lNode);

		// TODO:
//	     (if try mem (fst(dest_const l)) ["real_of_num"; "int_of_num"]
//         with Failure _ -> false
//      then () else pp_print_space fmt ());

		node.addBranch(spaceNode);
		
		TermPrinterTree rNode = print_term(r, 1000);
		node.addBranch(rNode);
		
		return node;
	}
}
