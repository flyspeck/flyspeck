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

October 8, 2008
Local settings: To run, you need to set the string propertiesFile in Constants.java to the path of anghel.properties (or whatever properties file is in used).

May 6, 2009
I'm having memory slow-down.  I'm now trying
java -Xms300m -Xmx1g graph/Generator  

June 21, 2009
The archive now has an interface.  It is selected at the top of the Generator.java file
To get the number of distinct hash codes:
grep "\"" kepler2009.out2 | cut -f1 -d" " | sort -u | wc   
grep "\"" kepler2009.out2 | cut -f1 -d" " | sort | uniq -c | grep -v " 1 "
