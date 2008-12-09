//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

#ifndef error_c
#define error_c

/* 
CLASS
	error

	Some primitive error reporting routines

OVERVIEW TEXT
	The class error contains some primitive error reporting routines.
	When the program terminates a procedure prints out the total
	number of errors reported.

*/

class error 
{
public:
		//////////
		// print out the current time to standard output
		//
static void printTime();  

		///////////
		// prints the current time and a message
		//
static void printTime(const char* s); 

		///////////
		// prints an error message
		//
static void message(const char*); 

		//////////
		// prints the total number of errors.
		//
static void diagnostic();
};

#endif
