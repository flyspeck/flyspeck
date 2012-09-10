package edu.pitt.math.jhol.ssreflect.parser;

import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.Reader;
import java.util.ArrayList;

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
		 * Adds a proof step (a tactic)
		 */
		public void addProofStep(TacticNode tac) {
			proof.add(tac);
		}
		
		/**
		 * Translates the lemma
		 */
		public void translate(PrintWriter out) {
			StringBuffer buffer = new StringBuffer(1000);
			String name = getName();
			
			out.println();
			// Comments
			out.println("(* Lemma " + name + " *)");
			
			// Statement
			buffer.append("let " + name + " = section_proof ");
			node.translateParameters(buffer);
			out.println(buffer);

			out.println(node.getGoalText());

			// Proof
//			buffer.append(" [");
			out.println('[');
			
			for (TacticNode tac : proof) {
				out.print("   ");
				out.print(tac.toHOLCommand());
				out.println(';');
			}
			
			out.println("];;");
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
		public void finalizeSection(PrintWriter out) {
			// Do not finalize lemmas in the initial section
			if (initialSection)
				return;
				
			out.println();
			out.println("(* Finalization of the section " + name + " *)");
			
			for (String lemma : lemmas) { 
				out.println("let " + lemma + " = finalize_theorem " + lemma + ";;");
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
		if (t.value == "Proof") {
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
			if (t.value == "Abort" || t.value == "Qed") {
				boolean abortFlag = (t.value == "Abort");
			
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
	private Section processSection(SectionNode currentSection) throws Exception {
		Section section = new Section(currentSection);
		String name = section.getName();
		
		// Start the section
		if (currentSection != null) {
			out.println();
			out.println("(* Section " + name + " *)");
			out.println(currentSection.toHOLCommand() + ";;");
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
					
					section.finalizeSection(out);
					out.println(sectionNode.toHOLCommand() + ";;");
					
					return section;
				} 
				else {
					// New section
					Section newSection = processSection(sectionNode);
					section.addAllLemmas(newSection);
				}
				
				continue;
			}
			
			// Lemma
			if (node instanceof LemmaNode) {
				Lemma lemma = processLemmaProof((LemmaNode) node);
				if (lemma != null) {
					lemma.translate(out);
					section.addLemmaName(lemma.getName());
				}
				
				continue;
			}
			
			out.println(node.toHOLCommand() + ";;");
		}
	}
	
	
	/**
	 * Compiles the input
	 */
	public void compile() throws Exception {
		try {
			moduleFlag = false;
			processSection(null);
			
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
