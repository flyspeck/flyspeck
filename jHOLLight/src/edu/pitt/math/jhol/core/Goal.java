package edu.pitt.math.jhol.core;

import java.util.ArrayList;

import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;

/**
 * Goal
 */
public class Goal extends CamlObject {
	// List of assumptions (and labels)
	private final ArrayList<Pair<String, Theorem>> assumptions;
	
	// Goal term
	private final Term goalTerm;
	
	
	/**
	 * Constructor
	 */
	public Goal(ArrayList<Pair<String, Theorem>> assumptions, Term goalTerm) {
		this.goalTerm = goalTerm;
		this.assumptions = new ArrayList<Pair<String,Theorem>>(assumptions);
	}
	
	
	/**
	 * Returns the goal term
	 */
	public Term goalTerm() {
		return goalTerm;
	}
	
	
	/**
	 * Returns the number of assumptions
	 */
	public int numberOfAssumptions() {
		return assumptions.size();
	}
	
	
	/**
	 * Returns the i-th assumption
	 */
	public Pair<String, Theorem> getAssumptions(int i) {
		return assumptions.get(i);
	}


	@Override
	public CamlType camlType() {
		return CamlType.GOAL;
	}


	@Override
	public String makeCamlCommand() {
		throw new RuntimeException("Goal cannot be used in a Caml expression");
	}


	@Override
	public String toCommandString() {
		throw new RuntimeException("Goal cannot be used in a Caml expression");
	}
	
	
	// Object methods
	
	@Override
	public int hashCode() {
		return assumptions.hashCode() + goalTerm.hashCode();
	}
	
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		
		if (obj == null)
			return false;
		
		if (!(obj instanceof Goal))
			return false;
		
		Goal obj2 = (Goal) obj;
		return assumptions.equals(obj2.assumptions) && goalTerm.equals(obj2.goalTerm);
	}
	
	
	@Override
	public String toString() {
		StringBuilder str = new StringBuilder();
		
		str.append("Goal(");
		str.append("Assumptions[");
		for (int i = 0; i < assumptions.size(); i++) {
			Pair<String, Theorem> p = assumptions.get(i);
			str.append(p.getFirst());
			str.append(":");
			str.append(p.getSecond());
			str.append("; ");
		}
		
		str.append("],");
		str.append(goalTerm);
		str.append(')');
		
		return str.toString();
	}
}
