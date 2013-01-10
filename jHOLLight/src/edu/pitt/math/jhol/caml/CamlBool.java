package edu.pitt.math.jhol.caml;

/**
 * An integer number
 */
public class CamlBool extends CamlObject {
	public final boolean val;
	
	/**
	 * Constructor
	 */
	public CamlBool(boolean val) {
		this.val = val;
	}

	@Override
	public CamlType camlType() {
		return CamlType.BOOL;
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
		if (val)
			return 7;
		else
			return 3;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (!(obj instanceof CamlBool))
			return false;
		
		CamlBool obj2 = (CamlBool) obj;
		return val == obj2.val;
	}
	
	@Override
	public String toString() {
		return String.valueOf(val);
	}

	@Override
	public String toRawString() {
		return String.valueOf(val);
	}
	
	
}
