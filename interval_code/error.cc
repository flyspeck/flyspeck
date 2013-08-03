//  copyright (c) 1997, Thomas C. Hales, all rights reserved.


// error.c // Thomas C. Hales // Jan 1996
// This contains a error-handling procedures


extern "C" {
#include <stdlib.h>
#include <time.h>
  // #include <sys/time.h>
}
#include <cstdlib>
#include <unistd.h>
#include <iostream>
#include "error.h"




using namespace std;

static int ERROR_COUNT=0;
static int CORNER_COUNT=0;

static  double timelimit =0.0;
static time_t start = clock();

void error::set_overtime(double millisec) {
  timelimit = millisec;
}

double error::cpu_millisecs() {
  time_t end = clock();
  return (1000.0 * (((double) (end - start)) / CLOCKS_PER_SEC));
}

void error::halt_overtime() {
  time_t end = clock();
  if (timelimit > 0.0 && (cpu_millisecs() > timelimit))
    {
      cout << "Too LONG msecs=" << timelimit << "; Bailing out..."<< endl<< flush;
      exit(0);
    }
}





void error::printTime()
        {
        cout << time(0) << endl << flush;
        }

void error::printTime(const char* s)
        {
        cout << s << " " << time(0) << endl << flush;
        }

void error::inc_corner() {
  CORNER_COUNT++;
}

int error::get_error_count() { return ERROR_COUNT; }

int error::get_corner_count() { return CORNER_COUNT; }

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
	

struct timeval Timer::start()
    {
        gettimeofday(&this->timer[0], NULL);
        return this->timer[0];
    }

struct timeval Timer::stop()
    {
        gettimeofday(&this->timer[1], NULL);
        return this->timer[1];
    }

int Timer::duration() const
    {
        int secs(this->timer[1].tv_sec - this->timer[0].tv_sec);
        int usecs(this->timer[1].tv_usec - this->timer[0].tv_usec);

        if(usecs < 0)
        {
            --secs;
            usecs += 1000000;
        }

        return static_cast<int>(secs * 1000 + usecs / 1000.0 + 0.5);
    }



class errorWrapup 
{
public:
	~errorWrapup();
};

errorWrapup::~errorWrapup () { diagnostic(); }

static errorWrapup Ewrapup;
