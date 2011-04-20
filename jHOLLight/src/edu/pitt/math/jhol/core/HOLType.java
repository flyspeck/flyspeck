package edu.pitt.math.jhol.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;


import edu.pitt.math.jhol.caml.CamlObject;
import edu.pitt.math.jhol.caml.CamlType;
import edu.pitt.math.jhol.core.printer.TypePrinter;


/**
 * Represents a HOL Light type
 * @author Alexey
 *
 */
public abstract class HOLType extends CamlObject {
	// Description of all type constants
	private static final HashMap<String, Pair<String, Integer>> typeConstants;
	
	
	// Static initialization
	static {
		// Initialize type constants
		typeConstants = new HashMap<String, Pair<String,Integer>>();
		// Add two basic types
		typeConstants.put("bool", new Pair<String, Integer>("bool", 0));
		typeConstants.put("fun", new Pair<String, Integer>("fun", 2));
	}
	
	
	@Override
	public final CamlType camlType() {
		return CamlType.HOL_TYPE;
	}
	
	
	@Override
	public String toCommandString() {
		StringBuilder str = new StringBuilder();
		str.append("`:");
		str.append(TypePrinter.printType(this));
		str.append("`");
		
		return str.toString();
	}
	
	
	/**
	 * Lookup function for type constants. Returns arity if it succeeds
	 */
	public static Integer get_type_arity(String name) {
		if (typeConstants.containsKey(name))
			return typeConstants.get(name).getSecond();
		
		return null;
	}
	
	
	/**
	 * Declares a new type
	 */
	public static void new_type(String name, int arity) throws Exception {
		if (get_type_arity(name) != null) {
			throw new Exception("new_type: type " + name + " has already been declared");
		}
		
		// Add a new type constant
		typeConstants.put(name, new Pair<String, Integer>(name, arity));
	}
	
	
	/**
	 * Constructs a type variable of the given name
	 */
	public static HOLType mk_vartype(String name) {
		return new TyVar(name);
	}
	
	
	/**
	 * Returns true if the given type is a type variable
	 */
	public static boolean is_vartype(HOLType type) {
		return type instanceof TyVar;
	}
	

	
	/**
	 * Constructs a type
	 */
	public static HOLType mk_type(String name, HOLType ... args) throws Exception {
/*		Integer arity = get_type_arity(name);
		if (arity == null)
			throw new Exception("mk_type: type " + name + " has not been defined");
		
		if (arity != args.length)
			throw new Exception("mk_type: wrong number of arguments to " + name);
*/		
		return new TyApp(name, args);
	}
	
	
	public static HOLType mk_type(String name) throws Exception {
		return mk_type(name, new ArrayList<HOLType>());
	}
	
	
	public static HOLType mk_type(String name, Collection<HOLType> args) throws Exception {
		return new TyApp(name, args);
	}
	
	
	public static HOLType mk_fun_ty(HOLType ty1, HOLType ty2) throws Exception {
		return mk_type("fun", ty1, ty2);
	}
	
	
	/**
	 * Type destructor
	 */
	public abstract Pair<String, HOLType[]> dest();
	
	
	/**
	 * Computes a type instantiation to match the given type
	 */
	public abstract ArrayList<Pair<HOLType, HOLType>> type_match(HOLType cty, ArrayList<Pair<HOLType, HOLType>> env);
	
	
	/**
	 * Type variable
	 */
	public static class TyVar extends HOLType {
		// Name of the type variable
		private final String name;
		
		private TyVar(String name) {
			this.name = name;
		}
		

	
		
		@Override
		public Pair<String, HOLType[]> dest() {
			return new Pair<String, HOLType[]>(name, null);
		}
		
		
		@Override
		public ArrayList<Pair<HOLType,HOLType>> type_match(HOLType cty, ArrayList<Pair<HOLType,HOLType>> env) {
			if (env == null)
				env = new ArrayList<Pair<HOLType,HOLType>>();
			
			HOLType tmp = Utils.rev_assoc(this, env);
			
			ArrayList<Pair<HOLType,HOLType>> result = new ArrayList<Pair<HOLType,HOLType>>();
			if (tmp == null) {
				result.add(new Pair<HOLType,HOLType>(cty, this));
				result.addAll(env);
				return result;
			}
			
			if (tmp.equals(cty))
				return env;
			
			return null;
		}
		
		
		@Override
		public String makeCamlCommand() {
			StringBuilder cmd = new StringBuilder();
			cmd.append("mk_vartype");
			cmd.append(' ');
			cmd.append('"');
			cmd.append(name);
			cmd.append('"');
			
			return cmd.toString();
		}


		// Override Object functions
		
		@Override
		public int hashCode() {
			return name.hashCode();
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			
			if (obj == null)
				return false;
			
			if (!(obj instanceof TyVar))
				return false;
			
			return name.equals(((TyVar) obj).name);
		}
		
		@Override
		public String toString() {
			return name;
		}
	}
	
	
	/**
	 * Type application
	 */
	public static class TyApp extends HOLType {
		// Name of the type constructor (type constant)
		private final String constructorName;
		
		// Arguments
		private final ArrayList<HOLType> args;
		
		private TyApp(String name, Collection<HOLType> args) {
			this.constructorName = name;
			this.args = new ArrayList<HOLType>(args);
		}
		
		private TyApp(String name, HOLType ... args) {
			this.constructorName = name;
			this.args = new ArrayList<HOLType>();
			for (HOLType arg : args) {
				this.args.add(arg);
			}
		}
		

		@Override
		public Pair<String, HOLType[]> dest() {
			HOLType[] a = new HOLType[args.size()];
			return new Pair<String, HOLType[]>(constructorName, args.toArray(a));
		}
		
		
		@Override
		public ArrayList<Pair<HOLType,HOLType>> type_match(HOLType cty, ArrayList<Pair<HOLType,HOLType>> env) {
			if (env == null)
				env = new ArrayList<Pair<HOLType,HOLType>>();
			
			if (is_vartype(cty))
				return null;
			
			Pair<String, HOLType[]> p1 = dest();
			Pair<String, HOLType[]> p2 = cty.dest();
			
			String vop = p1.getFirst();
			String cop = p2.getFirst();
			HOLType[] vargs = p1.getSecond();
			HOLType[] cargs = p2.getSecond();
			
			if (!vop.equals(cop))
				return null;

			if (vargs.length != cargs.length)
				return null;
			
			int n = vargs.length;
			ArrayList<Pair<HOLType,HOLType>> result = new ArrayList<Pair<HOLType,HOLType>>();
			result.addAll(env);
			
			for (int i = n - 1; i >= 0; i--) {
				result = vargs[i].type_match(cargs[i], result);
				if (result == null)
					return null;
			}
			
			return result;
		}
		
		
		@Override
		public String makeCamlCommand() {
			StringBuilder cmd = new StringBuilder();
			cmd.append("mk_type");
			cmd.append('(');
			
			cmd.append('"');
			cmd.append(constructorName);
			cmd.append('"');
			
			cmd.append(',');
			
			cmd.append('[');
			int n = args.size();
			for (int i = 0; i < n; i++) {
				cmd.append(args.get(i).makeCamlCommand());
				if (i < n - 1)
					cmd.append(';');
			}
			
			cmd.append(']');
			cmd.append(')');

			return cmd.toString();
		}
		

		// Override Object functions
		
		@Override
		public int hashCode() {
			return constructorName.hashCode() + 57 * args.hashCode();
		}
		
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			
			if (obj == null)
				return false;
			
			if (!(obj instanceof TyApp))
				return false;
			
			TyApp obj2 = (TyApp) obj;
			return constructorName.equals(obj2.constructorName) &&
				   args.equals(obj2.args);
		}
		
		
		@Override
		public String toString() {
/*			StringBuilder str = new StringBuilder();
			
			str.append(constructorName);
			
			str.append('[');
			int n = args.size();
			for (int i = 0; i < n; i++) {
				str.append(args.get(i));
				if (i < n - 1)
					str.append("; ");
			}
			str.append(']');
			
			return str.toString();*/
			return TypePrinter.printType(this);
		}
	}
}
