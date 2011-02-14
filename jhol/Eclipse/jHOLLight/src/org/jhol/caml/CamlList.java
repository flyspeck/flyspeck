package org.jhol.caml;

import java.util.Arrays;
import java.util.Collection;

/**
 * Represents a Caml list
 */
public class CamlList extends CamlObject {
	// List elements
	private final CamlObject[] elements;
	
	private final CamlType elementType;
	
	private int hash = -1;
	
	
	/**
	 * Constructor
	 */
	public CamlList(CamlType elementType, Collection<CamlObject> objs) {
		this.elements = new CamlObject[objs.size()];
		objs.toArray(elements);
		this.elementType = elementType;
		
		for (CamlObject x : elements) {
			if (!x.camlType().equals(elementType))
				throw new RuntimeException("CamlList: inconsistent types");
		}
	}
	
	
	/**
	 * Constructor
	 */
	public CamlList(CamlType elementType, CamlObject ... objs) {
		this.elements = Arrays.copyOf(objs, objs.length);
		this.elementType = elementType;
		
		for (CamlObject x : elements) {
			if (!x.camlType().equals(elementType))
				throw new RuntimeException("CamlList: inconsistent types");
		}
	}

	
	/**
	 * Returns the type of elements in the list
	 */
	public CamlType getElementType() {
		return elementType;
	}
	
	
	/**
	 * Returns the number of elements in the list
	 */
	public int size() {
		return elements.length;
	}
	
	
	/**
	 * Returns the i-th element in the list
	 */
	public CamlObject get(int i) {
		return elements[i];
	}
	
	
	@Override
	public CamlType camlType() {
		return new CamlType.ListType(elementType);
	}

	@Override
	public String makeCamlCommand() {
		StringBuilder str = new StringBuilder();
		str.append('[');
		
		for (int i = 0; i < elements.length; i++) {
			str.append(elements[i].makeCamlCommand());
			if (i < elements.length - 1)
				str.append("; ");
		}
		
		str.append(']');
		
		return str.toString();
	}

	@Override
	public String toCommandString() {
		StringBuilder str = new StringBuilder();
		str.append('[');
		
		for (int i = 0; i < elements.length; i++) {
			str.append(elements[i].toCommandString());
			if (i < elements.length - 1)
				str.append("; ");
		}
		
		str.append(']');
		
		return str.toString();
	}
	
	
	// Object methods
	
	@Override
	public int hashCode() {
		if (hash == -1) {
			hash = 11;
			for (CamlObject obj : elements) {
				hash ^= obj.hashCode();
			}
		}
		
		return hash;
	}
	
	
	@Override
	public boolean equals(Object obj) {
		if (obj == this)
			return true;
		if (obj == null)
			return false;
		if (!(obj instanceof CamlList))
			return false;
		
		CamlList obj2 = (CamlList) obj;
		return elementType.equals(obj2.elementType) && elements.equals(obj2.elements);
	}
	
	@Override
	public String toString() {
		StringBuilder str = new StringBuilder();
		str.append('[');
		
		for (int i = 0; i < elements.length; i++) {
			str.append(elements[i]);
			if (i < elements.length - 1)
				str.append("; ");
		}
		
		str.append(']');
		
		return str.toString();	
	}
}
