/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* ========================================================================== */

//  copyright (c) 1997, Thomas C. Hales, all rights reserved.


// interval (TCH Jan 1996)

/*  This gives a new data type interval, with controlled precision
	(interval) arithmetic.

    If the interval contains zero, division
	by the interval is NaN.

*/

#include <iostream>
extern "C"
{
#include <math.h>
#include <assert.h>
#include <time.h>
#include <stdlib.h>
#include <float.h>
#include <time.h>
#include <string.h>
}
#include "error.h"
#include "notPortable.h"
#include "interval.h"



interval interMath::min(interval a,interval b) 
	{ double t;
	  t = ((inf(a) >  inf(b)) ? inf(b) : inf(a));
	  return interval(t,t);
	}

interval interMath::min(interval a,interval b,interval c) 
	{ return interMath::min(a,interMath::min(b,c)); }

interval interMath::min(interval a,interval b,interval c,interval d) 
	{ return interMath::min(a,b,interMath::min(c,d)); }

interval interMath::max(interval a,interval b) 
	{ double t;
	  t = ((sup(a) < sup(b)) ? sup(b) : sup(a) );
	  return interval(t,t);
	}

interval interMath::max(interval a,interval b,interval c) 
	{ return interMath::max(a,interMath::max(b,c)); }

interval interMath::max(interval a,interval b, interval c,interval d) 
	{ return interMath::max(a,b,interMath::max(c,d)); }

// rounding modes:

volatile void interMath::nearest()
	{
	ROUND_NEAR;
	}

// It is not intended for the output to accurately reflect
// the actual interval.  We merely give a rough approximation.
// User beware!

ostream &operator<< (ostream & stream,interval c) 
	{ 
	//interMath::nearest();
        // if (c.hi-c.lo<1.0e-10) stream << c.hi;
	//stream.precision(18);
	stream << "{" << c.lo << "," << c.hi << "}";
	if (c.hi<c.lo) error::message("inverted interval in << ");
	return stream;
	}

interval interval::wideInterval(const char *ch1,const char *ch2)
	{
	interval t;
	interMath::down();
	t.lo =double(atof(ch1)) - DBL_MIN;
	interMath::up();
	t.hi = double(atof(ch2)) + DBL_MIN;
	return t;
	}

/* This constructor is not provably an interval containing the decimal represented by
   the string ch1.  For example, if an integer is given that is too large to be
   represented as an integer, this will fail.  It should be fully accurate for input
   within a determinable domain.
 */
interval::interval(const char *ch1) 
	{
	  interval t = wideInterval(ch1,ch1);
	  lo = t.lo;
	  hi = t.hi;
          if (strchr(ch1,'.')==NULL) { 
	    lo = double(atoi(ch1));
	    hi = lo;
	  }
	}

interval interval::slow_multiply(interval t2) const
	{
	interval t;
	
	if (lo>0.0)
		{
		if (t2.lo>0.0)
			{
			interMath::up(); t.hi=hi*t2.hi;
			interMath::down(); t.lo=lo*t2.lo;
			return t;
			}
		else if (t2.hi<0.0)
			{
			interMath::up(); t.hi= lo*t2.hi;
			interMath::down(); t.lo = hi*t2.lo;
			return t;
			}
		else 	{
			interMath::up(); t.hi = hi*t2.hi;
			interMath::down(); t.lo = hi*t2.lo;
			return t;
			}
		}

	else if (hi<0.0)
		{
		if (t2.hi<0.0)
			{
			interMath::up(); t.hi=lo*t2.lo;
			interMath::down(); t.lo=hi*t2.hi;
			return t;
			}
		else if (t2.lo>0.0)
			{
			interMath::up(); t.hi=hi*t2.lo;
			interMath::down(); t.lo=lo*t2.hi;
			return t;
			}
		else 
			{
			interMath::up(); t.hi= lo*t2.lo;
			interMath::down(); t.lo = lo*t2.hi;
			return t;
			}
		}

	else {
		if (t2.lo>0.0)
			{
			interMath::up(); t.hi = hi*t2.hi;
			interMath::down(); t.lo = lo*t2.hi;
			return t;
			}
		else if (t2.hi<0.0)
			{
			interMath::up(); t.hi = lo*t2.lo;
			interMath::down(); t.lo = hi*t2.lo;
			return t;
			}
		else
			{
			double tt;
			interMath::up(); t.hi = hi*t2.hi;
				  tt= lo*t2.lo;
				  if (tt>t.hi) t.hi=tt;
			interMath::down(); t.lo = lo*t2.hi;
			 	    tt = hi*t2.lo;
				    if (tt<t.lo) t.lo=tt;
			return t;
			}
		}
	} // end of * procedure

// use IEEE sqrt.
interval interMath::sqrt(interval a)  
	{
	interMath::up(); a.hi = (a.hi <= 0.0 ? 0.0 : ::sqrt(a.hi));
	interMath::down(); a.lo= (a.lo <= 0.0 ? 0.0 : ::sqrt(a.lo));
	return a;
	}

interval interMath::cuberoot(interval a)  
	{
	  interMath::up(); a.hi = pow(a.hi, 0.333333333334);
	  interMath::down(); a.lo= pow(a.lo,0.333333333333);
	return a;
	}


/*
   Now compute the arctangent.  Here there is no IEEE standard to fall back on.
   We use "Computer Approximations", John F. Hart et al. page 125 (s=4)
   The rational approximation to atan is given in  p 271 ArcTan 5032
*/

static double Atan1(double t) // atan(x) in the range [0..Tan[Pi/16]]
	{
	//assertion: |Atan1(x) - \arctan(x)| < 10^-13 on [0,tan(pi/16)]
	//assertion: floating point error in Atan1,Atan ||< 0.5e-13
	// the error term we use is extremely conservative:
	// it is added into atan at the end.
	static const double P00=  4.26665376811246382;
	static const double P01 = 3.291955407318148;
	static const double P02 = 0.281939359003812;
	static const double Q00 = 4.26665376811354027;
	static const double Q01 = 4.714173328637605 ;
	double t1 = t*t;
	double t2 = t1*t1;
	return t*(t1*P01 + t2*P02+P00)/(t1*Q01+t2+Q00);
	}

static double Atan(double x)
	{
	static const double tanpi_16 = 0.198912367379658006911597622645;
	static       double tan2pi_16= 0.41421356237309504880168872421;
	static const double tan3pi_16= 0.668178637919298919997757686523;
	// static const double tan4pi_16= 1.0;
	static const double tan5pi_16= 1.49660576266548901760113513494;
	static       double tan6pi_16= 2.41421356237309504880168872421;
	static const double tan7pi_16= 5.0273394921258481045149750711;
 
	static       double c2pi_16= 1.0+tan6pi_16*tan6pi_16;
	static       double c6pi_16= 1.0+tan2pi_16*tan2pi_16;
 
	static const double pi2_16=0.39269908169872415480783042291;
	static const double pi4_16=0.78539816339744830961566084582;
	static const double pi6_16=1.17809724509617246442349126873;
	static const double pi8_16=1.57079632679489661923132169164;
 
	if (x>=0.0)
	{
	if (x< tanpi_16) return( Atan1(x) );
	else if (x < tan3pi_16) 
		return Atan1(tan6pi_16 - c2pi_16/(x+tan6pi_16))+ pi2_16;
	else if (x < tan5pi_16)
		return Atan1(1.0 - 2.0/(x+1.0))+ pi4_16;
	else if (x < tan7pi_16)
		return Atan1(tan2pi_16  - c6pi_16/(x+tan2pi_16))+ pi6_16;
	else return Atan1(-1.0/x) + pi8_16;
	}
	else return -Atan(-x);
	}

interval interMath::atan(interval a)
	{
	interMath::nearest();
	static double arctan_error = 1.0e-10;
	return interval(
		Atan(inf(a))-arctan_error, Atan(sup(a))+arctan_error
		       );
	}

interval interMath::combine(interval x,interval y)
        {
        return interval(inf(min(x,y)),sup(max(x,y)));
        }


static double rand01()
	{
	static int w =0;
	if (w==0) { srand(time(0)); w = 1; }
	double u = double(rand());
    double v = double(/*stdlib.h*/RAND_MAX); 
	return u/v;
	}


void interMath::selfTest() {
	static int intervalTestCount =0;
    if (intervalTestCount>0) return;
    intervalTestCount++;
	cout << " -- loading interval routines \n" << flush;

	/*  string constructor */
	{
	  char* s = "3.1415926535897932384626433832795";
	  interval t = s;
	  cout.precision(30);
	  assert(t.lo < t.hi);
	}

	/* integer string constructor */
	{
	  char* s = "1";
	  interval t = s;
	  assert(t.lo == 1);
	  assert(t.hi == 1);
	}

	/* illustrate limitations of string constructor */
	{
	  char* s = "10000000000000000";
	  interval t = s;
	  interval u( "2147483647"); // overflow value.
	  assert(t.lo == u.lo);
	}

	/* underflow and overflow tests */ {
	double t = DBL_MAX;
	interMath::down();
	t = 2*t;
	assert(t==t);
	interMath::up();
	t = DBL_MIN;
	for (int i=0;i<1000;i++) t = t/2;
	assert(t==t);
	assert(t>0);
	}

	/* multiplication test */ {
	assert(interval(2.0,4.0)*interval(3.0,4.0)==interval(6.0,16.0));
	assert(interval(-1.0,4.0)*interval(3.0,7.0)==interval(-7.0,28.0));
	}

	/* rounding mode test */ {
	interval v(DBL_MIN,DBL_MIN);
	v = v+interval("1");
	assert(interMath::inf(v)==1.0);
	assert(interMath::sup(v)==1.0+DBL_EPSILON);
	}

	/* divison test */ {
	interval v = interval("1")/interval("6");
	v = v*interval("6");
	assert(interMath::inf(v)<1.0);
	assert(interMath::sup(v)>1.0);
	}

	/* square root test*/ {
	interval v = interMath::sqrt("2");
	v = v*v;
	assert(interMath::inf(v)<2.0);
	assert(interMath::sup(v)>2.0);
	assert((interMath::sup(v)-interMath::inf(v))/DBL_EPSILON <= 12);
	}

	/* rand01 test */ {
	double t = 0,u =0;
	for (int i=0;i<500;i++) { u=rand01(); t = (u>t?u:t); }
	assert(t>0.9); assert(t<=1.0);
	}

	/* interval multiplication */ {
	for (int i=0;i<5;i++)
		{
		cout.precision(30);
		double t1=rand01()-0.5,t2=rand01()-0.5,s1=rand01()-0.5,s2=rand01()-0.5;
		double t;
		if (t2<t1) { t = t1; t1=t2; t2=t; }
		if (s2<s1) { t = s1; s1=s2; s2=t; }
		interval x(t1,t2),y(s1,s2),z=x*y;
		interMath::up();
		t = t1*s1; 
		if (t1*s2>t) t = t1*s2;
		if (t2*s1>t) t = t2*s1;
		if (t2*s2>t) t = t2*s2;
		if ( interMath::sup(z) != t) 
			{
		    cout << t1 << " " << t2 << " " << s1 << " " << s2 << endl << flush;
			cout << z << endl << flush;
			cout << " "<< t << endl << endl << flush;
			}
		interMath::down();
		t = t1*s1; 
		if (t1*s2<t) t = t1*s2;
		if (t2*s1<t) t = t2*s1;
		if (t2*s2<t) t = t2*s2;
		if ( interMath::inf(z) != t) 
			{
		    cout << t1 << " " << t2 << " " << s1 << " " << s2 << endl << flush;
			cout << z << endl << flush;
			cout << " "<< t << endl << endl << flush;
			}
		}
	}

}
