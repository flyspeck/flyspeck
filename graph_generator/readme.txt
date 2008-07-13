Notes on the graph08 version of the graph generator.

Started with graph00 from Kepler diskimage 05 on April 25, 2008.
Edited to update assert to jassert (which is now a keyword in java).

Managing the path:
http://www.ibm.com/developerworks/library/j-classpath-unix/

Use -d to compile classes to a separate directory.
graph08/src$ javac -d ../classes graph/Generator.java 
cd ../classes
java graph/Generator

util/Config.java reads in the properties file.
It is set through the identifier propertiesFile in graph/Constants.java.
The path of this file must be edited to fit the local path before you run
the program.

July 12, 2008
New directory created with rendering.
All references to rendering have been removed from the graphics directory.
The rendering material hasn't been compiled or checked.  The code
will probably have to be tweaked a bit to make it runnable from this new directory.





