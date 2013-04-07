package edu.pitt.math.jhol.ssreflect.parser;

import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.Reader;
import java.util.ArrayList;

import edu.pitt.math.jhol.caml.CamlEnvironment;
import edu.pitt.math.jhol.ssreflect.parser.tree.LemmaNode;
import edu.pitt.math.jhol.ssreflect.parser.tree.ModuleNode;
import edu.pitt.math.jhol.ssreflect.parser.tree.Node;
import edu.pitt.math.jhol.ssreflect.parser.tree.SectionNode;
import edu.pitt.math.jhol.ssreflect.parser.tree.TacticNode;

/**
 * Converts the Coq-Ssreflect like text into HOL Light commands
 */
public class Compiler {
	// The main output stream
	private final PrintWriter out;
	// Input stream scanner
	private final Scanner scanner;
	// The main parser
	private final TreeBuilder builder;
	
	// A global module flag 
	private boolean moduleFlag;
	
	// Describes a lemma
	private static class Lemma {
		private final LemmaNode node;
		private final ArrayList<TacticNode> proof;
		
		/**
		 * Default constructor
		 */
		public Lemma(LemmaNode node) {
			assert (node != null);
			this.node = node;
			this.proof = new ArrayList<TacticNode>();
		}
		
		/**
		 * Returns lemma's name
		 */
		public String getName() {
			return node.getName();
		}
		
		/**
		 * Returns true if the lemma is a local section lemma
		 */
		public boolean isLet() {
			return node.isLet();
		}
		
		/**
		 * Adds a proof step (a tactic)
		 */
		public void addProofStep(TacticNode tac) {
			proof.add(tac);
		}
		
		/**
		 * Translates the lemma
		 */
		public void translate(PrintWriter out, CamlEnvironment env) throws Exception {
			StringBuffer buffer = new StringBuffer(1000);
			String name = getName();
			boolean letFlag = isLet();
			
			out.println();
			// Comments
			if (letFlag) {
				out.println("(* Let " + name + " *)");
			}
			else {
				out.println("(* Lemma " + name + " *)");
			}
			
			// Statement
			if (letFlag) {
				buffer.append("Sections.add_section_lemma " + '"' + name + '"');
				buffer.append(" (");
			}
			else {
				buffer.append("let " + name + " = ");
			}
			buffer.append("Sections.section_proof ");
			node.translateParameters(buffer);
			buffer.append('\n');

			buffer.append(node.getGoalText());
			buffer.append('\n');

			// Proof
			buffer.append("[\n");
			
			for (TacticNode tac : proof) {
				buffer.append("   ");
				buffer.append(tac.toHOLCommand(env));
				buffer.append(";\n");
			}
			
			buffer.append(']');
			if (letFlag) {
				buffer.append(')');
			}
			buffer.append(";;");
			
			String cmd = buffer.toString();
			out.println(cmd);
			
			if (env != null) {
				env.runCommand(cmd);
			}
		}
	}
	
	
	// Describes a section
	private static class Section {
		// True for the initial section
		private final boolean initialSection;
		// Name
		private final String name;
		// Names of lemmas in the section
		private final ArrayList<String> lemmas;
		
		/**
		 * Default constructor
		 */
		public Section(SectionNode sectionNode) {
			this.initialSection = (sectionNode == null);			
			this.name = (sectionNode != null ? sectionNode.getName() : "init_section");
			this.lemmas = new ArrayList<String>();
		}
		
		/**
		 * Returns section's name
		 */
		public String getName() {
			return name;
		}
		
		/**
		 * Adds a lemma into the section
		 */
		public void addLemmaName(String lemmaName) {
			lemmas.add(lemmaName);
		}
		
		/**
		 * Adds all lemmas of another (nested) section
		 */
		public void addAllLemmas(Section section) {
			lemmas.addAll(section.lemmas);
		}
		
		/**
		 * Finalizes the section
		 */
		public void finalizeSection(PrintWriter out, CamlEnvironment env) throws Exception {
			// Do not finalize lemmas in the initial section
			if (initialSection)
				return;
				
			out.println();
			out.println("(* Finalization of the section " + name + " *)");
			
			for (String lemma : lemmas) {
				String cmd = "let " + lemma + " = Sections.finalize_theorem " + lemma + ";;"; 
				out.println(cmd);
				
				if (env != null) {
					env.runCommand(cmd);
				}
			}
		}
	}
	
	
	/**
	 * Default constructor
	 */
	public Compiler(Reader in, OutputStream out) {
		this.scanner = new Scanner(in);
		this.builder = new TreeBuilder(scanner);
		this.out = new PrintWriter(out);
	}
	
	
	/**
	 * Interprets commands in the "proof" mode
	 */
	private Lemma processLemmaProof(LemmaNode lemmaNode) throws Exception {
		Lemma lemma = new Lemma(lemmaNode);
		Token t = scanner.peekToken();
		
		// Initial 'Proof' command (optional)
		if (t.value == "Proof" || t.value == "proof") {
			// Proof
			scanner.nextToken();
			
			// Should be .
			t = scanner.nextToken();
			if (t.type != TokenType.PERIOD)
				throw new Exception(". expected: " + t);
		}
		
		// Process a proof
		while (true) {
			t = scanner.peekToken();
			
			// Special commands
			if (t.value == "Abort" || t.value == "Qed" || t.value == "abort" || t.value == "qed") {
				boolean abortFlag = (t.value == "Abort" || t.value == "abort");
			
				// Abort or Qed
				scanner.nextToken();

				// Should be .
				t = scanner.nextToken();
				if (t.type != TokenType.PERIOD)
					throw new Exception(". expected: " + t);

				// The lemma is aborted
				if (abortFlag)
					return null;
			
				return lemma;
			}
		
			TacticNode tac = builder.parseProof();
			
			// .
			t = scanner.nextToken();
			if (t.type != TokenType.PERIOD)
				throw new Exception(". expected: " + t);
			
			lemma.addProofStep(tac);
		}
	}
	

	/**
	 * Processes a section
	 */
	private Section processSection(SectionNode currentSection, CamlEnvironment env) throws Exception {
		Section section = new Section(currentSection);
		String name = section.getName();
		String cmd;
		
		// Start the section
		if (currentSection != null) {
			out.println();
			out.println("(* Section " + name + " *)");
			cmd = currentSection.toHOLCommand(env) + ";;";
			out.println(cmd);
			
			if (env != null) {
				env.runCommand(cmd);
			}
		}

		// Process all commands in the section
		while (true) {
			Token t = scanner.peekToken();
			if (t.type == TokenType.EOF) {
				if (currentSection == null)
					return null;
				
				throw new Exception("The section " + name + " is not closed: " + t);
			}
			
			Node node = builder.parseGlobal();
			// .
			t = scanner.nextToken();
			if (t.type != TokenType.PERIOD)
				throw new Exception(". expected: " + t);
			
			// Module
			if (node instanceof ModuleNode) {
				if (currentSection != null)
					throw new Exception("A module cannot be declared inside a section");
				
				if (moduleFlag)
					throw new Exception("Only one module can be declared");
				
				if (env == null)
					throw new Exception("Modules are not supported in fast compilation");
			
				// Start the module
				String moduleName = ((ModuleNode) node).getName();
				out.println();
				out.println("(* Module " + moduleName + "*)");
				out.println("module " + moduleName + " = struct");
				out.println();
				
				moduleFlag = true;
				continue;
			}
			
			// Section
			if (node instanceof SectionNode) {
				SectionNode sectionNode = (SectionNode) node;

				// End section
				if (!sectionNode.isStartSection()) {
					if (currentSection == null)
						throw new Exception("No open section: " + t);
					
					if (!name.equals(sectionNode.getName()))
						throw new Exception("The open section has the name " + name + ": " + t);
					
					section.finalizeSection(out, env);
					cmd = sectionNode.toHOLCommand(env) + ";;";
					out.println(cmd);
					if (env != null) {
						env.runCommand(cmd);
					}
					
					return section;
				} 
				else {
					// New section
					Section newSection = processSection(sectionNode, env);
					section.addAllLemmas(newSection);
				}
				
				continue;
			}
			
			// Lemma
			if (node instanceof LemmaNode) {
				Lemma lemma = processLemmaProof((LemmaNode) node);
				if (lemma != null) {
					lemma.translate(out, env);
					if (!lemma.isLet()) {
						section.addLemmaName(lemma.getName());
					}
				}
				
				continue;
			}
			
			// A raw HOL Light command
			cmd = node.toHOLCommand(env) + ";;";
			out.println(cmd);
			if (env != null) {
				env.runCommand(cmd);
			}
		}
	}
	
	
	/**
	 * Compiles the input
	 */
	public void compile(CamlEnvironment env) throws Exception {
		try {
			moduleFlag = false;
			processSection(null, env);
			
			// Close the module (if it is declared)
			if (moduleFlag) {
				out.println();
				out.println("(* Close the module *)");
				out.println("end;;");
			}
		}
		finally {
			out.flush();
		}
	}
	
}
