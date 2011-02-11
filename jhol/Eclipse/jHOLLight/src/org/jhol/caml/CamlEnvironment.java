package org.jhol.caml;

/**
 * Caml environment for executing Caml commands
 */
public abstract class CamlEnvironment {
	/**
	 * Executes the given command and returns the result as a CamlObject
	 */
	public abstract CamlObject execute(String command) throws Exception;
	
	public abstract CamlObject execute(String command, CamlType returnType) throws Exception;
	
	/**
	 * Executes the given (raw) command
	 */
	public abstract void runCommand(String rawCommand) throws Exception;
}
