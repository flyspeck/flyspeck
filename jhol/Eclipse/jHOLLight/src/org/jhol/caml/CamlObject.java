package org.jhol.caml;

import org.jhol.core.Theorem;

/**
 * Abstract Caml object
 */
public abstract class CamlObject {
	/**
	 * Returns the type of the object
	 */
	public abstract CamlType camlType();


	/**
	 * Returns the argument type of this object if the object is a function
	 * @return null if the object is not a function
	 */
	public final CamlType argType() {
		CamlType type = camlType();
		
		if (!(type instanceof CamlType.FunctionType))
			return null;
		
		return ((CamlType.FunctionType) type).getArgType();
	}
	
	
	/**
	 * Returns the result of the application of this object (if it is a function)
	 * to another object
	 * @param arg
	 * @return null if the object is not a function
	 * @throws an exception if the argument type is incorrect
	 */
	public final CamlObject apply(CamlObject arg) throws Exception {
		CamlType expectedType = argType();
		if (expectedType == null)
			return null;

		return new CamlApplication(this, arg);
	}
	
	
	/**
	 * Creates a Caml command, evaluates it, and returns the result as a CamlObject
	 * @param env
	 * @return
	 */
	public CamlObject eval(CamlEnvironment env) throws Exception {
		throw new Exception("CamlObject.eval: the operation is not defined");
	}
	
	
	/**
	 * Returns a Caml command corresponding to the object
	 */
	public abstract String makeCamlCommand();
	
	
	/**
	 * Application of a function to an argument
	 */
	public static class CamlApplication extends CamlObject {
		private final CamlObject f;
		private final CamlObject arg;
		
		private final CamlType type;
		
		/**
		 * Private constructor
		 */
		private CamlApplication(CamlObject f, CamlObject arg) throws Exception {
			this.f = f;
			this.arg = arg;
			
			CamlType fType = f.camlType();
			CamlType argType = arg.camlType();
			
			if (!(fType instanceof CamlType.FunctionType))
				throw new Exception("CamlApplication: f is not a function: " + f);
			
			CamlType.FunctionType fType2 = (CamlType.FunctionType) fType;
			if (!argType.equals(fType2.getArgType()))
				throw new Exception("CamlApplication: incompatible types: " + f + ", " + arg);

			this.type = fType2.getReturnType();
		}
		
		@Override
		public CamlType camlType() {
			return type;
		}


		@Override
		public CamlObject eval(CamlEnvironment env) throws Exception {
			if (type instanceof CamlType.FunctionType)
				throw new Exception("CamlApplication.eval: evaluation works only for non-function objects");
			
			String cmd = makeCamlCommand();
			CamlObject result = env.execute(cmd);
			
			// TODO: find better solution
			if (result instanceof Theorem.TempTheorem) {
				((Theorem.TempTheorem) result).setCommand(this);
			}
			
			return result;
		}

		
		
		@Override
		public String makeCamlCommand() {
			StringBuilder cmd = new StringBuilder();

			cmd.append('(');
			cmd.append(f.makeCamlCommand());
			cmd.append(')');
			
			cmd.append('(');
			cmd.append(arg.makeCamlCommand());
			cmd.append(')');
			
			return cmd.toString(); 
		}
		
		
		@Override
		public int hashCode() {
			return f.hashCode() + 17 * arg.hashCode();
		}
		
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof CamlApplication))
				return false;
			
			CamlApplication obj2 = (CamlApplication) obj;
			return f.equals(obj2.f) && arg.equals(obj2.arg);
		}
		
		
		@Override
		public String toString() {
			StringBuilder str = new StringBuilder();
			str.append('(');
			str.append(f);
			str.append(')');
			str.append('(');
			str.append(arg);
			str.append(')');
			
			return str.toString();
		}
	}
}
