package org.jhol.caml;

/**
 * Describes a Caml type
 */
public abstract class CamlType {
	/* Constants for simple types */
	public static final CamlType TYPE = new HOLTypeType();
	public static final CamlType TERM = new TermType();
	public static final CamlType THM = new TheoremType();
	
	
	/**
	 * Function type
	 */
	public static class FunctionType extends CamlType {
		private final CamlType argType;
		private final CamlType returnType;
		
		public FunctionType(CamlType argType, CamlType returnType) {
			if (argType == null || returnType == null)
				throw new RuntimeException("FunctionType: null arguments");
			
			this.argType = argType;
			this.returnType = returnType;
		}
		
		
		public CamlType getArgType() {
			return argType;
		}
		
		
		public CamlType getReturnType() {
			return returnType;
		}
		
		
		@Override
		public int hashCode() {
			return argType.hashCode() + 31 * returnType.hashCode();
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof FunctionType))
				return false;
			
			FunctionType obj2 = (FunctionType) obj;
			return argType.equals(obj2.argType) && returnType.equals(obj2.returnType);
		}
		
		@Override
		public String toString() {
			StringBuilder str = new StringBuilder();
			str.append('(');
			str.append(argType);
			str.append(')');
			str.append("->");
			str.append('(');
			str.append(returnType);
			str.append(')');
			
			return str.toString();
		}
	}
	
	
	/**
	 * HOL type
	 */
	public static class HOLTypeType extends CamlType {
		private HOLTypeType() {
		}
		
		@Override
		public int hashCode() {
			return 23;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof HOLTypeType))
				return false;
		
			return true;
		}
		
		@Override
		public String toString() {
			return "type";
		}
	}
	
	
	/**
	 * Term type
	 */
	public static class TermType extends CamlType {
		private TermType() {
		}
		
		@Override
		public int hashCode() {
			return 11;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof TermType))
				return false;
		
			return true;
		}
		
		@Override
		public String toString() {
			return "term";
		}
	}
	
	
	/**
	 * Theorem type
	 */
	public static class TheoremType extends CamlType {
		private TheoremType() {
		}
		
		@Override
		public int hashCode() {
			return 13;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof TheoremType))
				return false;
		
			return true;
		}
		
		@Override
		public String toString() {
			return "thm";
		}
	}

	
	/**
	 * List type
	 */
	public static class ListType extends CamlType {
		private final CamlType elementType;
		
		
		public ListType(CamlType elementType) {
			if (elementType == null)
				throw new RuntimeException("ListType: null argument");
			
			this.elementType = elementType;
		}
		
		
		public CamlType getElementType() {
			return elementType;
		}
		
		@Override
		public int hashCode() {
			return elementType.hashCode() * 17;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof ListType))
				return false;
			
			ListType obj2 = (ListType) obj;
		
			return elementType.equals(obj2.elementType);
		}
		
		@Override
		public String toString() {
			StringBuilder str = new StringBuilder();
			str.append("list");
			str.append('(');
			str.append(elementType);
			str.append(')');
			
			return str.toString();
		}
	}
	
}
