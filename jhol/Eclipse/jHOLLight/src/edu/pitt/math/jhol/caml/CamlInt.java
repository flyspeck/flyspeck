package edu.pitt.math.jhol.caml;

/**
 * An integer number
 */
public class CamlInt extends CamlObject {
	public final int val;
	
	/**
	 * Constructor
	 */
	public CamlInt(int val) {
		this.val = val;
	}

	@Override
	public CamlType camlType() {
		return CamlType.INT;
	}

	@Override
	public String makeCamlCommand() {
		return String.valueOf(val);
	}

	@Override
	public String toCommandString() {
		return String.valueOf(val);
	}
	
	
	// Object methods
	
	@Override
	public int hashCode() {
		return val; 
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (!(obj instanceof CamlInt))
			return false;
		
		CamlInt obj2 = (CamlInt) obj;
		return val == obj2.val;
	}
	
	@Override
	public String toString() {
		return String.valueOf(val);
	}
	
	
}
