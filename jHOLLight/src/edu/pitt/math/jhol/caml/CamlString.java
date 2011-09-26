package edu.pitt.math.jhol.caml;

/**
 * A string
 */
public class CamlString extends CamlObject {
	public final String str;
	
	/**
	 * Constructor
	 */
	public CamlString(String str) {
		this.str = str;
	}

	@Override
	public CamlType camlType() {
		return CamlType.STRING;
	}

	@Override
	public String makeCamlCommand() {
		// TODO: replace " in the string with \"
		return '"' + str + '"';
	}

	@Override
	public String toCommandString() {
		return '"' + str + '"';
	}
	
	
	// Object methods
	
	@Override
	public int hashCode() {
		return str.hashCode();
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (!(obj instanceof CamlString))
			return false;
		
		CamlString obj2 = (CamlString) obj;
		return str.equals(obj2.str);
	}
	
	@Override
	public String toString() {
		return '"' + str + '"';
	}

	@Override
	public String toRawString() {
		return '"' + str + '"';
	}
	
	
}
