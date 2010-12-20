/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* ========================================================================== */

//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

#ifdef _interval_h
#ifndef _interval_inline_h
#define _interval_inline_h
#include "error.h"

inline interval interMath::pos(interval x) { x.hi = ((x.hi<0.0)? 0.0:x.hi);
                                  x.lo = ((x.lo<0.0)? 0.0:x.lo);
                                  return x; }


inline double interMath::sup(interval x) { return x.hi; }
inline double interMath::inf(interval x) { return x.lo; }
inline double interMath::abs(interval x) { return sup(max(x,-x)); }

inline interval::interval(double a,double b)
        {
        lo=a; hi=b;
        }

inline int interval::operator==(interval a) const
        { return ((a.lo==lo)&&(a.hi==hi)); }

inline int interval::zero() const
        { return ((lo==0.0)&&(hi==0.0)); }

inline int interval::operator<(interval a) const
	{ return (hi<a.lo); }

inline int interval::operator>(interval a) const
	{ return (lo>a.hi); }

inline volatile void interMath::up() {  ROUND_UP;  }

inline volatile void interMath::down() {  ROUND_DOWN;  }

inline interval interval::operator+(interval t2) const
        {
        interval t;
        interMath::up(); t.hi = hi+t2.hi;
        interMath::down(); t.lo = lo+ t2.lo;
        return t;
        }

inline interval interval::operator-(interval t2) const
        {
        interval t;
        interMath::up(); t.hi = hi-t2.lo;
        interMath::down(); t.lo = lo- t2.hi;
        return t;
        }

// assumption: no round-off occurs in unary negation: rounding mode not set.
inline interval interval::operator-() const
        {
	return interval(-hi,-lo);
        }

inline interval interval::operator/(interval t2) const
	{
	//
	interval t;
	if (interMath::boundedFromZero(t2))
		{
		interMath::up(); t.hi = 1.0/t2.lo;
		interMath::down(); t.lo = 1.0/t2.hi;
		return (*this)*t;
		}
	//throw unstable::x; 
	error::printTime("division by zero encountered"); 
	cout << t2.lo << " " << t2.hi << endl << flush;
	throw unstable::x;
	}

inline int interMath::boundedFromZero(const interval& t)
    { return ((t.hi> -/*float.h*/DBL_EPSILON)&&(t.lo<DBL_EPSILON)) ? 0 : 1; }

	// optimized for multiplication of positives
	// Warning: we are using the passed parameter as a local variable.
	//
inline interval interval::operator*(interval t2) const
	{
	return ((lo>0)&&(t2.lo>0 ))
	? ( interMath::up(), t2.hi = hi*t2.hi, 
		interMath::down(), t2.lo=lo*t2.lo, t2) 
	: slow_multiply(t2);
	}

#endif
#endif
