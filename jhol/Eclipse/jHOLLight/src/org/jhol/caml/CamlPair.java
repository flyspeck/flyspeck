package org.jhol.caml;

/**
 * Represents a Caml pair
 */
public class CamlPair extends CamlObject {
	private final CamlObject a, b;
	
	
	/**
	 * Constructor
	 */
	public CamlPair(CamlObject a, CamlObject b) {
		this.a = a;
		this.b = b;
	}
	
	
	/**
	 * Returns the first element
	 */
	public CamlObject first() {
		return a;
	}
	
	/**
	 * Returns the second element
	 */
	public CamlObject second() {
		return b;
	}
	
	
	@Override
	public CamlType camlType() {
		return new CamlType.PairType(a.camlType(), b.camlType());
	}

	@Override
	public String makeCamlCommand() {
		StringBuilder str = new StringBuilder();
		str.append("((");
		str.append(a.makeCamlCommand());
		str.append("),(");
		str.append(b.makeCamlCommand());
		str.append("))");
		
		return str.toString();
	}

	@Override
	public String toCommandString() {
		StringBuilder str = new StringBuilder();
		str.append("(");
		str.append(a.toCommandString());
		str.append("),(");
		str.append(b.toCommandString());
		str.append(")");
		
		return str.toString();
	}
	
	
	// Object methods
	
	@Override
	public int hashCode() {
		return a.hashCode() + 17 * b.hashCode();
	}
	
	
	@Override
	public boolean equals(Object obj) {
		if (obj == this)
			return true;
		if (obj == null)
			return false;
		if (!(obj instanceof CamlPair))
			return false;
		
		CamlPair obj2 = (CamlPair) obj;
		return a.equals(obj2.a) && b.equals(obj2.b);
	}
	
	@Override
	public String toString() {
		StringBuilder str = new StringBuilder();
		str.append("Pair(");
		str.append(a);
		str.append("),(");
		str.append(b);
		str.append(")");
		
		return str.toString();	
	}
}
