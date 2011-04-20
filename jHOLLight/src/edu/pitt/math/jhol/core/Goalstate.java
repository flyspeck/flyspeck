package edu.pitt.math.jhol.core;

import java.util.ArrayList;
import java.util.Collection;

import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;

/**
 * A goal state (a list of goals)
 */
public class Goalstate extends CamlObject {
	// Goals
	private final ArrayList<Goal> goals;
	
	/**
	 * Constructor
	 * @param goals
	 */
	public Goalstate(Collection<Goal> goals) {
		this.goals = new ArrayList<Goal>(goals);
	}
	
	
	/**
	 * Returns the number of goals in the state
	 */
	public int numberOfGoals() {
		return goals.size();
	}
	
	/**
	 * Returns the i-th goal
	 * @param i
	 * @return
	 */
	public Goal getGoal(int i) {
		return goals.get(i);
	}


	@Override
	public CamlType camlType() {
		return CamlType.GOAL_STATE;
	}


	@Override
	public String makeCamlCommand() {
		throw new RuntimeException("Goalstate cannot be used in a Caml expression");
	}


	@Override
	public String toCommandString() {
		throw new RuntimeException("Goalstate cannot be used in a Caml expression");
	}
	
	
	// Object methods
	
	@Override
	public int hashCode() {
		return goals.hashCode() * 57;
	}
	
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		
		if (obj == null)
			return false;
		
		if (!(obj instanceof Goalstate))
			return false;
		
		Goalstate obj2 = (Goalstate) obj;
		return goals.equals(obj2.goals);
	}
	
	
	@Override
	public String toString() {
		StringBuilder str = new StringBuilder();
		
		str.append("Goalstate(");
		for (int i = 0; i < goals.size(); i++) {
			str.append(goals.get(i));
			if (i < goals.size() - 1)
				str.append(',');
		}
		str.append(')');
		
		return str.toString();
	}
}
