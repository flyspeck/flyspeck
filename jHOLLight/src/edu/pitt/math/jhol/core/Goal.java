package edu.pitt.math.jhol.core;

import java.util.ArrayList;

import edu.pitt.math.jhol.caml.CamlList;
import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlPair;
import edu.pitt.math.jhol.caml.CamlString;
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
	 * Returns all free variables in the goal
	 */
	public ArrayList<Term> getContextVariables() {
		ArrayList<Term> frees = goalTerm.frees();
		
		for (int i = 0; i < assumptions.size(); i++) {
			ArrayList<Term> frees1 = assumptions.get(i).getSecond().concl().frees();
			frees.removeAll(frees1);
			frees.addAll(frees1);
		}
		
		return frees;
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
	
	
	/**
	 * Returns the assumption with the given name
	 * @return null if no assumption with the given name exists
	 */
	public Theorem getAssumptions(String name) {
		return Utils.assoc(name, assumptions);
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


	@Override
	public String toRawString() {
		StringBuffer str = new StringBuffer("Goal(");

		ArrayList<CamlPair> objs = new ArrayList<CamlPair>();
		for (int i = 0; i < assumptions.size(); i++) {
			Pair<String, Theorem> p = assumptions.get(i);
			CamlPair pair = new CamlPair(new CamlString(p.getFirst()), p.getSecond());
			objs.add(pair);
		}
		
		CamlList list = new CamlList(new CamlType.PairType(CamlType.STRING, CamlType.THM), objs);
		str.append(list.toRawString());
		str.append(',');
		str.append(goalTerm.toRawString());
		str.append(')');
		
		return str.toString();
	}
}
