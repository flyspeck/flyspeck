package edu.pitt.math.jhol.core;

import java.util.ArrayList;

import static edu.pitt.math.jhol.core.Term.*;

/**
 * Basic functions for terms
 */
public class TermUtils {
	/**
	 * Returns the body of the given abstraction
	 */
	public static Term body(Term tm) {
		if (!is_abs(tm))
			return null;
		
		return dest_abs(tm).getSecond();
	}

	/**
	 * Returns the operand from a combination
	 */
	public static Term rand(Term tm) {
		Pair<Term, Term> p = dest_comb(tm);
		if (p == null)
			return null;
		
		return p.getSecond();
	}
	
	
	/**
	 * Returns the operator from a combination
	 */
	public static Term rator(Term tm) {
		Pair<Term, Term> p = dest_comb(tm);
		if (p == null)
			return null;
		
		return p.getFirst();
	}
	
	
	/**
	 * Destroys a generalized abstraction
	 */
	public static Pair<Term, Term> dest_gabs(Term tm) {
		if (is_abs(tm)) {
			return dest_abs(tm);
		}
		
		Pair<Term, Term> lr = dest_comb(tm);
		if (lr == null)
			return null;
		
		Term l = lr.getFirst();
		Term r = lr.getSecond();
		if (!is_const(l))
			return null;
		
		if (!dest_const(l).getFirst().equals("GABS"))
			return null;
		
		Term br = body(r);
		if (br == null)
			return null;

		Pair<Term, Term> ltm_rtm = dest_binary("GEQ", strip_binder("!", br).getSecond());
		if (ltm_rtm == null)
			return null;
		
		Term rand_ltm = rand(ltm_rtm.getFirst());
		if (rand_ltm == null)
			return null;
		
		return new Pair<Term, Term>(rand_ltm, ltm_rtm.getSecond());
	}
	
		
	/**
	 * Returns true if the term is a generalized abstraction
	 */
	public static boolean is_gabs(Term tm) {
		return dest_gabs(tm) != null;
	}
	
	
	/**
	 * Iteratively breaks apart combinations
	 */
	public static Pair<Term, ArrayList<Term>> strip_comb(Term t) {
		ArrayList<Term> args = new ArrayList<Term>();
		
		while (true) {
			if (!is_comb(t))
				return new Pair<Term, ArrayList<Term>>(t, args);
			
			Pair<Term,Term> p = dest_comb(t);
			args.add(0, p.getSecond());
			t = p.getFirst();
		}
	}
	
	
	/**
	 * Destroy the given binary operation
	 */
	public static Pair<Term, Term> dest_binary(String opName, Term tm) {
		if (!is_comb(tm))
			return null;
		
		Pair<Term, Term> p = dest_comb(tm);
		Term rator = p.getFirst();
		Term r = p.getSecond();
		if (!is_comb(rator))
			return null;
		
		p = dest_comb(rator);
		Term c = p.getFirst();
		if (!is_const(c))
			return null;
		
		if (!dest_const(c).getFirst().equals(opName))
			return null;
		
		return new Pair<Term, Term>(p.getSecond(), r);
	}
	
	
	/**
	 * Destroys the given binder
	 */
	public static Pair<Term, Term> dest_binder(String binderName, Term tm) {
		Pair<Term, Term> p = dest_comb(tm);
		if (p == null)
			return null;
		
		if (!is_const(p.getFirst()))
			return null;
		
		if (!dest_const(p.getFirst()).getFirst().equals(binderName))
			return null;
		
		return dest_abs(p.getSecond());
	}
	
	/**
	 * Iteratively breaks apart the given binder
	 */
	public static Pair<ArrayList<Term>, Term> strip_binder(String binderName, Term tm) {
		ArrayList<Term> binders = new ArrayList<Term>();
		
		Term body = tm;
		
		while (true) {
			Pair<Term, Term> p = dest_binder(binderName, body);
			if (p == null)
				break;
			
			binders.add(p.getFirst());
			body = p.getSecond();
		}
		
		return new Pair<ArrayList<Term>, Term>(binders, body);
	}	
	

}
