//  copyright (c) 1997, Thomas C. Hales, all rights reserved.


// error.c // Thomas C. Hales // Jan 1996
// This contains a error-handling procedures


extern "C" {
#include <stdlib.h>
#include <time.h>
}
#include <iostream>
#include "error.h"

using namespace std;

static int ERROR_COUNT=0;

void error::printTime()
        {
        cout << time(0) << endl << flush;
        }

void error::printTime(const char* s)
        {
        cout << s << " " << time(0) << endl << flush;
        }

int error::get_error_count() { return ERROR_COUNT; }

void error::message(const char *s)
	{
	cout << "error(" << time(0) << "): " << s << "\n" << flush; //was cerr
	ERROR_COUNT++;
	if (ERROR_COUNT>200)
		{
		cout << "Too many errors. Bailing out..."<< endl<< flush;
		exit(0);
		}
	}

void error::fatal(const char* s)
{
  cout << "fatal error(" << time(0) << "): " << s << "\n" << flush;
  ERROR_COUNT++;
  exit(0);
}

static void diagnostic()
	{
	if (ERROR_COUNT>0)
	cout << "(errors: " << ERROR_COUNT << ")" << endl << flush;
	else cout << "(no errors)" << endl << flush;
	}

void error::diagnostic() { ::diagnostic(); }
	

class errorWrapup 
{
public:
	~errorWrapup();
};

errorWrapup::~errorWrapup () { diagnostic(); }

static errorWrapup Ewrapup;
