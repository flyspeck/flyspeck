package edu.pitt.math.jhol.caml;

/**
 * Describes a Caml type
 */
public abstract class CamlType {
	/* Constants for simple types */
	public static final CamlType STRING = new StringType();
	public static final CamlType INT = new IntType();
	public static final CamlType HOL_TYPE = new HOLTypeType();
	public static final CamlType TERM = new TermType();
	public static final CamlType THM = new TheoremType();
	public static final CamlType GOAL = new GoalType();
	public static final CamlType GOAL_STATE = new GoalstateType();
	public static final CamlType TACTIC = new TacticType();
	
	
	/**
	 * Returns the number of arguments of an object of this type
	 */
	public int numberOfArguments() {
		return 0;
	}
	
	
	/**
	 * Returns the type of the n-th argument (n is from 0 to numberOfArguments() - 1)
	 */
	public CamlType getArgType(int n) {
		return null;
	}
	
	
	/**
	 * Returns the return type of a function
	 * @return
	 */
	public CamlType getLastType() {
		return this; 
	}
	
	
	/**
	 * Returns the command for printing a Caml object of this type
	 */
	public abstract String getPrintCommand();
	
	
	/**
	 * Creates a function type
	 */
	public static FunctionType mk_function(CamlType argType, CamlType returnType) {
		return new FunctionType(argType, returnType);
	}
	
	
	/**
	 * Function type
	 */
	public static class FunctionType extends CamlType {
		private final CamlType argType;
		private final CamlType returnType;
		
		private FunctionType(CamlType argType, CamlType returnType) {
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
		public String getPrintCommand() {
			throw new RuntimeException("FuntionType: objects of this type are not allowed");
		}

		
		
		@Override
		public int numberOfArguments() {
			return 1 + returnType.numberOfArguments();
		}
		
		
		@Override
		public CamlType getLastType() {
			return returnType.getLastType();
		}
		
		
		@Override
		public CamlType getArgType(int n) {
			if (n == 0)
				return argType;
			
			return returnType.getArgType(n - 1);
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
			str.append("Fun");
			str.append('(');
			str.append(argType);
			str.append(',');
			str.append(returnType);
			str.append(')');
			
			return str.toString();
		}
	}
	

	/**
	 * String
	 */
	public static class StringType extends CamlType {
		private StringType() {
		}

		@Override
		public String getPrintCommand() {
			return "raw_string_of_string";
		}
		
		@Override
		public int hashCode() {
			return 47;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof StringType))
				return false;
		
			return true;
		}
		
		@Override
		public String toString() {
			return "String";
		}
	}
	
	
	/**
	 * Int
	 */
	public static class IntType extends CamlType {
		private IntType() {
		}

		@Override
		public String getPrintCommand() {
			return "raw_string_of_int";
		}
		
		@Override
		public int hashCode() {
			return 79;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof IntType))
				return false;
		
			return true;
		}
		
		@Override
		public String toString() {
			return "Int";
		}
	}

	
	/**
	 * Tactic
	 */
	public static class TacticType extends CamlType {
		private TacticType() {
		}

		@Override
		public String getPrintCommand() {
			throw new RuntimeException("TacticType: objects of this type are not allowed");
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
			if (!(obj instanceof TacticType))
				return false;
		
			return true;
		}
		
		@Override
		public String toString() {
			return "Tactic";
		}
	}

	
	
	/**
	 * Goal
	 */
	public static class GoalType extends CamlType {
		private GoalType() {
		}

		@Override
		public String getPrintCommand() {
			return "raw_string_of_goal";
		}
		
		@Override
		public int hashCode() {
			return 71;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof GoalType))
				return false;
		
			return true;
		}
		
		@Override
		public String toString() {
			return "Goal";
		}
	}
	
	
	/**
	 * Goal state
	 */
	public static class GoalstateType extends CamlType {
		private GoalstateType() {
		}

		@Override
		public String getPrintCommand() {
			return "raw_string_of_goalstate";
		}
		
		@Override
		public int hashCode() {
			return 73;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof GoalstateType))
				return false;
		
			return true;
		}
		
		@Override
		public String toString() {
			return "Goalstate";
		}
	}



	
	/**
	 * HOL type
	 */
	public static class HOLTypeType extends CamlType {
		private HOLTypeType() {
		}

		@Override
		public String getPrintCommand() {
			return "raw_string_of_type";
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
			return "HOLType";
		}
	}
	
	
	/**
	 * Term type
	 */
	public static class TermType extends CamlType {
		private TermType() {
		}
		
		@Override
		public String getPrintCommand() {
			return "raw_string_of_term";
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
			return "Term";
		}
	}
	
	
	/**
	 * Theorem type
	 */
	public static class TheoremType extends CamlType {
		private TheoremType() {
		}
		
		@Override
		public String getPrintCommand() {
			return "raw_string_of_thm";
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
			return "Theorem";
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
		public String getPrintCommand() {
			String type = '"' + elementType.toString() + '"';
			String cmd = "(" + elementType.getPrintCommand() + ")";
			return "raw_string_of_list " + type + " " + cmd;
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
			str.append("List");
			str.append('(');
			str.append(elementType);
			str.append(')');
			
			return str.toString();
		}
	}
	
	
	/**
	 * Pair type
	 */
	public static class PairType extends CamlType {
		private final CamlType a, b;
		
		
		public PairType(CamlType a, CamlType b) {
			if (a == null || b == null)
				throw new RuntimeException("PairType: null argument");
			
			this.a = a;
			this.b = b;
		}
		
		
		public CamlType getFirstType() {
			return a;
		}
		
		
		public CamlType getSecondType() {
			return b;
		}
		
		
		@Override
		public String getPrintCommand() {
			String cmd1 = "(" + a.getPrintCommand() + ")";
			String cmd2 = "(" + b.getPrintCommand() + ")";
			return "raw_string_of_pair " + cmd1 + " " + cmd2;
		}
		
		
		@Override
		public int hashCode() {
			return a.hashCode() + b.hashCode() * 31;
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof PairType))
				return false;
			
			PairType obj2 = (PairType) obj;
		
			return a.equals(obj2.a) && b.equals(obj2.b);
		}
		
		@Override
		public String toString() {
			StringBuilder str = new StringBuilder();
			str.append("Pair");
			str.append('(');
			str.append(a);
			str.append(',');
			str.append(b);
			str.append(')');
			
			return str.toString();
		}
		
	}
	
}
