package edu.pitt.math.jhol.ssreflect.parser.tree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import edu.pitt.math.jhol.core.Goal;
import edu.pitt.math.jhol.core.HOLType;
import edu.pitt.math.jhol.core.Pair;
import edu.pitt.math.jhol.core.Term;
import edu.pitt.math.jhol.core.Theorem;

/**
 * Provides the link between the active goal and the identifiers
 */
public class GoalContext {
	// Goal's free variables indexed by their names
	private final HashMap<String, Term> freeVariables;
	// Names of assumptions
	private final HashSet<String> assumptions;
	
	/**
	 * Default constructor
	 */
	public GoalContext(Goal goal) {
		freeVariables = new HashMap<String, Term>();
		assumptions = new HashSet<String>();

		// Get all free variables in the goal's context
		ArrayList<Term> free = goal.getContextVariables();
		for (Term tm : free) {
			assert(Term.is_var(tm));
			
			Pair<String, HOLType> var = Term.dest_var(tm);
			String name = var.getFirst();
			if (freeVariables.containsKey(name)) {
				System.err.println("Warning: two variables with the same name: " + name);
			}
			
			freeVariables.put(name, tm);
		}
		
		// Get names of all assumptions
		int n = goal.numberOfAssumptions();
		for (int i = 0; i < n; i++) {
			Pair<String, Theorem> assum = goal.getAssumptions(i);
			String label = assum.getFirst();
			if (assumptions.contains(label)) {
				System.err.println("Warning: two assumptions with the same label: " + label);
			}
			
			if (freeVariables.containsKey(label)) {
				System.err.println("Warning: a variable and an assumption with the same name: " + label);
			}
			
			assumptions.add(label);
		}
	}
	
	
	/**
	 * Returns a free variable with the given name
	 * @return null if there is no free variable with the given name
	 */
	public Term getFreeVariable(String name) {
		return freeVariables.get(name);
	}
	
	
	/**
	 * Returns true if the given label is the name of an assumption
	 * @param label
	 * @return
	 */
	public boolean isAssumptionName(String label) {
		return assumptions.contains(label);
	}
}
