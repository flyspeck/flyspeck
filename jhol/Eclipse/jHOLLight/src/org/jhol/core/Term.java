package org.jhol.core;

import java.util.ArrayList;

import org.jhol.caml.CamlObject;
import org.jhol.caml.CamlType;

/**
 * Abstract HOL term
 */
public abstract class Term extends CamlObject {
	/**
	 * Returns the corresponding Caml type (term)
	 */
	public final CamlType camlType() {
		return CamlType.TERM;
	}
	
	
	/**
	 * Creates a term from a raw string description
	 */
	public static Term create(String rawString) {
		throw new RuntimeException("Not implemented");
	}
	
	
	/**
	 * Creates a variable
	 */
	public static Term mk_var(String v, HOLType ty) {
		return new VarTerm(v, ty);
	}
	

	/**
	 * Creates a constant
	 */
	public static Term mk_const(String name, Pair<HOLType, HOLType> ... theta) throws Exception {
		// TODO: HOL implementation with the type substitution
//		return new ConstTerm(name, HOLType.)
		throw new Exception("Not implemented"); 
	}
	
	
	/**
	 * Creates a constant
	 */
	public static Term mk_mconst(String name, HOLType type) {
		return new ConstTerm(name, type);
	}
	
	
	/**
	 * Creates an abstraction
	 */
	public static Term mk_abs(Term bvar, Term bod) throws Exception {
		if (bvar instanceof VarTerm) {
			return new AbsTerm((VarTerm) bvar, bod);
		}
		
		throw new Exception("mk_abs: not a variable");
	}
	
	
	/**
	 * Creates a combination
	 */
	public static Term mk_comb(Term f, Term a) throws Exception {
		Pair<String, HOLType[]> tyf = f.type().dest();
		if (!tyf.getFirst().equals("fun"))
			throw new Exception("mk_comb: f is not a function");
		
		HOLType ty = tyf.getSecond()[0];
		HOLType tya = a.type();
		
		if (!ty.equals(tya))
			throw new Exception("mk_comb: types do not agree");
		
		return new CombTerm(f, a);
	}
	
	
	/**
	 * Finds the variables free in the term
	 */
	public abstract ArrayList<VarTerm> frees();
	
	/**
	 * Finds all variables in the term
	 */
	public abstract ArrayList<VarTerm> variables();
	
	
	/**
	 * Returns the type of the term
	 */
	public abstract HOLType type() throws Exception;
	
	/**
	 * Var term
	 */
	public static class VarTerm extends Term {
		// Variable's name
		private final String name;
		
		// Variable's type
		private final HOLType type;

		
		/**
		 * Private constructor
		 */
		private VarTerm(String name, HOLType type) {
			this.name = name;
			this.type = type;
		}
		
		
		@Override
		public HOLType type() {
			return type;
		}
		
		
		@Override
		public ArrayList<VarTerm> frees() {
			return variables();
		}
		
		@Override
		public ArrayList<VarTerm> variables() {
			ArrayList<VarTerm> result = new ArrayList<VarTerm>();
			result.add(this);
			return result;
		}
		
		
		@Override
		public String makeCamlCommand() {
			StringBuilder cmd = new StringBuilder();
			cmd.append("mk_var");
			cmd.append('(');

			cmd.append('"');
			cmd.append(name);
			cmd.append('"');
			
			cmd.append(',');
			
			cmd.append(type.makeCamlCommand());
			
			cmd.append(')');
			
			return cmd.toString();
		}
		
		
		
		// Override Object methods
		
		@Override
		public int hashCode() {
			return name.hashCode() + 31 * type.hashCode();
		}
		
		
		@Override
		public boolean equals(Object obj) {
			if (obj == this)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof VarTerm))
				return false;
			
			VarTerm obj2 = (VarTerm) obj;
			return name.equals(obj2.name) && type.equals(obj2.type);
		}
		
		
		@Override
		public String toString() {
			StringBuilder str = new StringBuilder();
			str.append("Var(");
			str.append(name);
			str.append(',');
			str.append(type);
			str.append(')');
			
			return str.toString();
		}
	}



	/**
	 * Const term
	 */
	public static class ConstTerm extends Term {
		// Constant's name
		private final String name;
		
		// Constant's type
		private final HOLType type;

		/**
		 * Private constructor
		 */
		private ConstTerm(String name, HOLType type) {
			this.name = name;
			this.type = type;
		}
		
		
		@Override
		public HOLType type() {
			return type;
		}
		

		@Override
		public ArrayList<VarTerm> frees() {
			return variables();
		}
		
		
		@Override
		public ArrayList<VarTerm> variables() {
			return new ArrayList<VarTerm>();
		}
		
		
		@Override
		public String makeCamlCommand() {
			StringBuilder cmd = new StringBuilder();
			cmd.append("mk_mconst");
			cmd.append('(');
			
			cmd.append('"');
			cmd.append(name);
			cmd.append('"');
			
			cmd.append(',');
			
			cmd.append(type.makeCamlCommand());
			cmd.append(')');
			
			return cmd.toString();
		}
		
		
		// Override Object methods
		
		@Override
		public int hashCode() {
			return name.hashCode() + 31 * type.hashCode();
		}
		
		
		@Override
		public boolean equals(Object obj) {
			if (obj == this)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof ConstTerm))
				return false;
			
			ConstTerm obj2 = (ConstTerm) obj;
			return name.equals(obj2.name) && type.equals(obj2.type);
		}
		
		
		@Override
		public String toString() {
			StringBuilder str = new StringBuilder();
			str.append("Const(");
			str.append(name);
			str.append(',');
			str.append(type);
			str.append(')');
			
			return str.toString();
		}
	}


	/**
	 * Comb term
	 */
	public static class CombTerm extends Term {
		// Application's operator
		private final Term rator;
		// Application's operand
		private final Term rand;

		/**
		 * Private constructor
		 */
		private CombTerm(Term rator, Term rand) {
			this.rator = rator;
			this.rand = rand;
		}
		

		@Override
		public HOLType type() throws Exception {
			HOLType ratorType = rator.type();
			return ratorType.dest().getSecond()[1];
		}
		
		@Override
		public ArrayList<VarTerm> frees() {
			ArrayList<VarTerm> ratorFrees = rator.frees();
			ArrayList<VarTerm> randFrees = rand.frees();
			
			// Take the union
			randFrees.removeAll(ratorFrees);
			ratorFrees.addAll(randFrees);

			return ratorFrees;
		}
		
		
		@Override
		public ArrayList<VarTerm> variables() {
			ArrayList<VarTerm> ratorVars = rator.variables();
			ArrayList<VarTerm> randVars = rand.variables();
			
			// Take the union
			randVars.removeAll(ratorVars);
			ratorVars.addAll(randVars);
			
			return ratorVars;
		}
		
		
		@Override
		public String makeCamlCommand() {
			StringBuilder cmd = new StringBuilder();
			
			cmd.append("mk_comb");
			cmd.append('(');
			cmd.append(rator.makeCamlCommand());
			cmd.append(',');
			cmd.append(rand.makeCamlCommand());
			cmd.append(')');
			
			return cmd.toString();
		}

		
		
		// Override Object methods
		
		@Override
		public int hashCode() {
			return rator.hashCode() + 31 * rand.hashCode();
		}
		
		
		@Override
		public boolean equals(Object obj) {
			if (obj == this)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof CombTerm))
				return false;
			
			CombTerm obj2 = (CombTerm) obj;
			return rator.equals(obj2.rator) && rand.equals(obj2.rand);
		}
		
		
		@Override
		public String toString() {
			StringBuilder str = new StringBuilder();
			str.append("Comb[");
			str.append(rator);
			str.append(',');
			str.append(rand);
			str.append(']');
			
			return str.toString();
		}
	}


	/**
	 * Abs term
	 * @author Alexey
	 *
	 */
	public static class AbsTerm extends Term {
		private final VarTerm var;
		private final Term body;
		
		/**
		 * Private constructor
		 */
		private AbsTerm(VarTerm var, Term body) {
			this.var = var;
			this.body = body;
		}
		
		@Override
		public HOLType type() throws Exception {
			HOLType varType = var.type();
			HOLType bodyType = body.type();
			
			return HOLType.mk_fun_ty(varType, bodyType);
		}
		
		@Override
		public ArrayList<VarTerm> frees() {
			ArrayList<VarTerm> result = body.frees();
			result.remove(var);
			
			return result;
		}
		
		
		@Override
		public ArrayList<VarTerm> variables() {
			ArrayList<VarTerm> result = body.variables();
			if (!result.contains(var))
				result.add(var);
			
			return result;
		}
		
		
		@Override
		public String makeCamlCommand() {
			StringBuilder cmd = new StringBuilder();
			
			cmd.append("mk_abs");
			cmd.append('(');
			cmd.append(var.makeCamlCommand());
			cmd.append(',');
			cmd.append(body.makeCamlCommand());
			cmd.append(')');
			
			return cmd.toString();
		}

		
		
		
		// Override Object methods
		
		@Override
		public int hashCode() {
			return var.hashCode() + 31 * body.hashCode();
		}
		
		
		@Override
		public boolean equals(Object obj) {
			if (obj == this)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof AbsTerm))
				return false;
			
			AbsTerm obj2 = (AbsTerm) obj;
			return var.equals(obj2.var) && body.equals(obj2.body);
		}
		
		
		@Override
		public String toString() {
			StringBuilder str = new StringBuilder();
			str.append("(\\");
			str.append(var);
			str.append('.');
			str.append(body);
			str.append(')');
			
			return str.toString();
		}
	}



	
}


