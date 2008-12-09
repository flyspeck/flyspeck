// Copyright (c) 1997, Thomas C. Hales, all rights reserved.


#ifndef _interval_h
#define _interval_h

#include <iostream.h>
#include "notPortable.h"

/*
CLASS
	interval

	A class representing real-valued intervals

OVERVIEW TEXT
	An interval is the the most important data structure in the kepler package.
	It represents a real-valued interval whose endpoints are exactly 
	representable by computer.   Basic arithmetic operations *,+,/,- are
	overloaded to give correctly rounded interval arithmetic. 

	Additional procedures for manipulating intervals are found in the
	interMath class.

	An <a href="http://cs.utep.edu/interval-comp/main.html">
	introduction</a> to interval arithmetic

	It is unworthy of excellent persons to lose hours like slaves in the labor
	of calculation.

	. . . Gottfried Wilhelm von Leibniz 
	
	Back to the 
	<a href="../index.html">Kepler</a>
	conjecture home page.

AUTHOR
	Thomas C. Hales
*/

class interval  
{
private: 
	interval slow_multiply(interval) const;

public:
	double lo;
	double hi;
		//////////
		// A standard constructor for intervals.
		// Intervals are general initialized by strings rather than
		// as decimal constants.  The rounding mode is set appropriately
		// when the string is converted to an interval, so that an interval
		// bracketing the decimal conversion of the string is obtained.
		//
		// We use strings because of untrustworthy things that compilers
		// do with doubles.  For example, on my Sun CC and SGI CC compilers
		// even if the rounding mode is set upward interMath::up(), we get
		// assert(1.0 == 1.0+DBL_MIN) even though DBL_MIN is positive.
		// Similarly, although claiming to be IEEE compliant, programs give
		// assert(1.0 == 1.00000000000000000001) even when the rounding
		// mode is directed upward.  It seems that constants are computed
		// at compile time, but rounding modes are set at run time, so
		// to get a reliable constant, we must wrap constants in a string until
		// run time.
		//
	interval(const char *); // construct with a string; interval("3.14"), etc.

		//////////
		// Another constructor for intervals
		// The first string is converted using downward rounding to the
		// lower bound of the interval.  The second string is rounding
		// up to a representable number giving the upper bound of the interval.
		//
	static interval wideInterval(const char *,const char *); // lo, hi

		//////////
		// Construct an interval from the endpoints.  Refer to the comments
		// for the string constructor to see the shortfalls of a double
		// type constructor.  This constructor should only be used on
		// doubles that are computed at run time using interval
		// arithmetic.
		//
	inline interval(double,double); // lo, hi

		//////////
		// This constructor does nothing
		//
	interval() {};

		//////////
		// Addition of intervals is based on IEEE rounding modes so that
		// the interval returned contains the sum of the two intervals.
		// 
	inline interval operator+(interval) const;

		//////////
		// Subtraction of intervals is based on IEEE rounding modes so that
		// the interval returned contains the difference of the two intervals.
		//
	inline interval operator-(interval) const;

		//////////
		// Multiplication of intervals is based on IEEE rounding modes so that
		// the interval returned contains the product of the two intervals.
		// Multiplication is performed inline if both intervals are
		// completely positive.  Otherwise, a long procedure with many
		// cases is called
		//
	inline interval operator*(interval) const;

		//////////
		// Division of intervals is based on IEEE rounding modes.  In the
		// current implementation x/y is computed as x times the reciprocal
		// of y.  If the interval y contains zero, an error message is
		// issued and zero is returned.
		// An extremely paranoid view is taken of division by zero.  If
		// the interval comes within float.h's DBL_EPSILON of zero, then
		// it is considered an error.  The user might want to change
		// the constant to something less paranoid, such as DBL_MIN.
		//
	inline interval operator/(interval) const;

		//////////
		// Unary negation of intervals.  This operation should be independent
		// of the rounding mode.
		//
	inline interval operator-() const;

		//////////
		// Is completely less than.  This relation is true only if
		// every element of the first interval is strictly less than
		// every element of the second.
		// 
	inline int operator<(interval) const; // completely less than 

		//////////
		// Is completely greater than.  This relation is true only if
		// every element of the first interval is strictly greater than
		// every element fo the second.
		//
	inline int operator>(interval) const; // completely greater than

		//////////
		//  Is identically equal to.  This relation between intervals
		//  is true if both endpoints are equal.
		//
	inline int operator==(interval) const;  // identically =

		////////
		// Output an interval.  The endpoints of the interval are printed
		// with the precision set at 18 digits.
		// 
	friend ostream &operator<< (ostream &stream,interval c);
 
};

/*

CLASS
	interMath

	Interval versions of standard math library functions

OVERVIEW TEXT
	The functions up(), down(), nearest() set the rounding modes for
	arithmetic operations.

	combine(interval,interval) gives the convex hull of two intervals
	abs(interval) is a double giving the maximum absolute value on the interval

AUTHOR
	Thomas C. Hales
	
*/

class interMath {
public:
		//////////
		// the return value is an interval of width zero
		//
	static interval min(interval,interval);  

		//////////
		// the return value is an interval of width zero
		//
	static interval min(interval,interval,interval);

		//////////
		// the return value is an interval of width zero
		//
	static interval min(interval,interval,interval,interval);
	
		//////////
		// the return value is an interval of width zero
		//
	static interval max(interval,interval);

		//////////
		// the return value is an interval of width zero
		//
	static interval max(interval,interval,interval);
		
		//////////
		// the return value is an interval of width zero
		//
	static interval max(interval,interval,interval,interval);
		
		//////////
		// the interval returned is the convex hull of the two that are given
		//
	static interval combine(interval,interval); 
	
		//////////
		// an interval square root function.  The square root function has
		// been extended to return 0 for negative values in the domain, so
		// that sqrt([-1,4]), for example, returns the interval [0,2].
		// The implementation makes use of the math.h sqrt library function.
		// The IEEE standard requires the library function to return a
		// correctly rounded result when the rounding modes are set.
		// 
	static interval sqrt(interval);  // negative values return 0

		//////////
		// An interval atan function.  The IEEE standard does not specify
		// the performance of the math.h atan library function.  As a result,
		// we have implemented our own from scratch.  This implementation
		// is based on an old book by John F. Hart, "Computer Approximations"
		// page 125 (s=4).  The rational approximation that we use is
		// given on page 271, ArcTan 5032.
		//
		// The routine uses the addition law for the arctangent to
		// reduce the argument to the interval [0,tan(pi/16)].  A rational
		// approximation to the arctangent is then used on the interval.
		// Explicit error bounds are known for this rational approximation.
		// The results of the rational approximation are padded with
		// a much-to-generous error term so that the interval returned
		// by the procedure is guaranteed to contain the arctangent
		// of the argument.
		//
		// The error term we have added is enormous (about 1.0e-10). It is
		// far larger than what the error analysis requires, and the user
		// of this function may wish to suppy a smaller error term.
		// 
	static interval atan(interval);

		//////////
		// the function [x,y] -> [max(0,x),max(0,y)]. The positive part of
		// an interval.
		//
	static inline interval pos(interval x); 

		//////////
		// the upper endpoint of an interval
		//
	static inline double sup(interval x); // (hi)

		//////////
		// the lower endpoint of an interval
		//
	static inline double inf(interval x); // (lo)

		//////////
		// the largest absolute value of any element in the interval
		//
	static inline double abs(interval x); 

		//////////
		// set the IEEE rounding mode to round-to-nearest.  The 
		// mode remains in force until the next mode change.
		//
	static volatile void nearest();

		//////////
		// set the IEEE rounding mode to round-up.  The mode
		// stays in effect until the next mode change.
		//
	static volatile void up();

		//////////
		// Set the IEEE rounding mode to round-down. The mode
		// stays in effect until the next mode change.
		//
	static volatile void down();

		//////////
		// Check to see if the interval can be safely used as
		// a denominator. This is the inline function called by
		// the interval division operator to determine whether
		// a division can be performed.
		//
	static inline int boundedFromZero(const interval&);

		//////////
		// Check that interval routines are running correctly.
		//
	static void selfTest();
};

#include "interval_inline.h"


#endif

