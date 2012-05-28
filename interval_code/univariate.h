/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 2010-09-07 */
/* ========================================================================== */


#ifndef univariate_
#define univariate_

#include <iomanip>
#include <iostream>
#include <tr1/unordered_map>
extern "C"
{
#include <math.h>
#include <stdlib.h>
}
#include "error.h"
#include "interval.h"


/*
CLASS
	univariate

	An interval-based linear approximation of univariate functions.

OVERVIEW TEXT

AUTHOR
	
	Thomas C. Hales
*/

class uniprimitive;

typedef tr1::unordered_map<uniprimitive*,interval> mapType;


class univariate
{
public: // for now
  mapType data;

public:

	//////////
	// Add a univariates to a given one.
	//
univariate operator+(const univariate&) const;

	//////////
	// Scale a univariate by a interval multiple.
	//
univariate operator*(const interval&) const;

	//////////
	// create a bitwise copy of a univariate
	//
univariate(const univariate&);

univariate(uniprimitive* ) ;

	//////////
	// assignment of a univariate
	//
//univariate operator=(const univariate& f);

	//////////
	// Deallocate memory:
	//
~univariate();

	//////////
	// Evaluate nth univariate derivative.
        // n=0 gives function value, n=1 gives first der, n>=2 gives second der.
        // No derivatives of order higher than 2 are provided.
	// 
 interval eval(const interval&,int n) const;

        // interval to interval version of matan.
static const interval matan(const interval& x) ;

	//////////
	// pow0 is the constant function taking value 1.
	// pow1 is the identity function,
	// pow_ is the nth power function,
        // atan,
        // cos, sin are restricted to the domain [-pi/2,pi/2].

        // matan modified arctan (sqrt x) / (sqrt x).  on (-1,infinty).
        // At 0, matan has a power series 1 - x/3 + x^2/5 ... 
        // with radius of convergence 1
        //
        // i_sqp is a spline upper bound on i_sqrt that is C^2 and extends beyond 0.
        // it is useful as a replacement for i_sqrt near 0.  It is not terribly accurate, but it is
        // very well behaved.  
        //
        // i_sqn is a spline lower bound on i_sqrt.
        // i_truncate_sqrt assumes that input >= c14, bounding arg away from 0.
	//
 static const univariate i_pow0,i_pow1, i_pow2,i_pow3,i_pow4,i_pow3h2,i_pow5h6,
   i_sqrt, i_truncate_sqrt, 
   i_sqp, i_sqn,i_atan, i_asin,i_acos, i_sin, i_cos, i_inv,
   i_matan;

	//////////
	// Check the correctness of univariate routines.
	//



static void selfTest();


};


#endif
