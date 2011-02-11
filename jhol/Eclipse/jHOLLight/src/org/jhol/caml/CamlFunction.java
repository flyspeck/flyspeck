package org.jhol.caml;

/**
 * A Caml function
 */
public class CamlFunction extends CamlObject {
	// Function's name
	private final String name;
	
	// Function's type
	private final CamlType type;

	
	/**
	 * Default constructor
	 */
	public CamlFunction(String name, CamlType type) {
		this.name = name;
		this.type = type;
	}
	
	
	@Override
	public CamlType camlType() {
		return type;
	}

	@Override
	public String makeCamlCommand() {
		return name;
	}

	@Override
	public String toCommandString() {
		return name;
	}
	
		
	// Object methods
	
	@Override
	public int hashCode() {
		return name.hashCode() + 53 * type.hashCode();
	}
	
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		
		if (obj == null)
			return false;
		
		if (!(obj instanceof CamlFunction))
			return false;
		
		CamlFunction obj2 = (CamlFunction) obj;
		return name.equals(obj2.name) && type.equals(obj2.type);
	}
	
	@Override
	public String toString() {
		return "(" + name + " : " + type + ")";
	}
}
