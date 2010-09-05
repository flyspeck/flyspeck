/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* ========================================================================== */

//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

#ifndef VOR
#define VOR

#include <iomanip>
#include <iostream>
extern "C"
{
#include <math.h>
#include <stdlib.h>
}
#include "error.h"
#include "interval.h"

using namespace std;
/* 
CLASS
	secondDerive

	Low level routines relating to the second derivative.  These
	should not generally be called directly by the end user.

OVERVIEW TEXT

	The class secondDerive contains a large number of static
	low level routines.  I do not see any reason that
	a user would want to call these routines directly.  They compute
	bounds on the second partial derivatives of various functions
	defined on a simplex.  This class is used by various
	Taylor approximation procedures to give rigorous upper and lower
	bounds on various functions.

	In the following routines x[] is the lower bound, 
	z[6] the upper on a cell.
	these are the edges squared, so that often they are in the range [4,8].

	Usually it is only the second deriviatives that are needed, but
	this usually requires computing the function value and the first
	derivatives as well, so often they are returned too.


AUTHOR

	Thomas C. Hales

*/

	


class secondDerive 
{
public:

		//////////
		// Give interval bounds on the second partial derivatives
		// of the function chi126. 
		//
		// The input is the upper and lower bounds on the cell.
		//
		// This procedure writes the partial derivatives to  DDf.
		//
		// 1 is the return value. Since chi126 is a polynomial, the 
		// computation will always be sucessful 
		// (unless outrageous arguments creating overflow are given). 
		//
		//
static int setChi126(const double x[6],const double z[6],interval DDf[6][6]);

		//////////
		// Give interval bounds on the second partial derivatives
		// of the function u126. 
		//
		// The input is the upper and lower bounds on the cell.
		//
		// This procedure writes the partial derivatives to DDf.
		//
		// 1 is the return value.  Since u126 is a polynomial, the 
		// computation will always be sucessful 
		// (unless outrageous arguments creating overflow are given). 
		//
		//
static int setU126(const double x[6],const double z[6], interval DDf[6][6]);

		//////////
		// Give interval bounds on the second partial derivatives
		// of the function u135. 
		//
		// The input is the upper and lower bounds on the cell.
		//
		// This procedure writes the partial derivatives to DDf.
		//
		// 1 is the return value.  Since u135 is a polynomial, the 
		// computation will always be sucessful. 
		// (unless outrageous arguments creating overflow are given). 
		//
		//
static int setU135(const double x[6],const double z[6], interval DDf[6][6]);

		//////////
		// Give interval bounds on the second derivatives of the
		// function delta. 
		//
		// The input is the upper and lower bounds on the cell.
		//
		// This procedure writes the partial derivatives to DDf.
		//
		// 1 is the return value.  Since delta is a polynomial, the 
		// computation will always be sucessful.
		// (unless outrageous arguments creating overflow are given). 
		//
		//
static int setDelta(const double x[6],const double z[6],interval DDf[6][6]);

		//////////
		// Give interval bounds on the function dih, and its
		// first and second partial derivatives.
		//
		// The input is the upper and lower bounds on the cell.
		//
		// This procedure writes the absolute value of the 
		// partial derivatives to DDf.
		//
		// If the derivatives were
		// sucessfully computed a nonzero value is returned.
		//
static int setAbsDihedral(const double x[6],const double z[6],double DDf[6][6]);

		//////////
		// Compute the second derivative of the dihedral angle.
		// The dihedral angle is that along the first edge of the simplex.
		// All mixed partial derivatives are computed.
		// 
		// Input lower and upper bounds x,z on the lengths squared of
		// the edges.  The function also inputs sqrt(delta) 
		// and its first and second derivatives in
		// s, Ds, DDs.  The function returns a nonzero value if 
		// the calculation is a success.  The dihedral angle, and
		// its first and second derivatives are placed in h,Dh, and DDh.
		//
static int setDihedral(const double x[6],const double z[6],const interval& s,
	const interval Ds[6],const interval DDs[6][6],
	interval& h,interval Dh[6],interval DDh[6][6]);


		//////////
		// Compute the second derivative of the dihedral2 angle.
		// The dihedral angle is that along the second edge of the simplex.
		// All mixed partial derivatives are computed.
		// 
		// Input lower and upper bounds x,z on the lengths squared of
		// the edges.  The function also inputs sqrt(delta) 
		// and its first and second derivatives in
		// s, Ds, DDs.  The function returns a nonzero value if 
		// the calculation is a success.  The dihedral angle, and
		// its first and second derivatives are placed in h,Dh, and DDh.
		//
static int setDih2(const double x[6],const double z[6],
	const interval& s,const interval Ds[6],const interval DDs[6][6],
	interval& h,interval Dh[6],interval DDh[6][6]);

		//////////
		// Compute the second derivative of the dihedral3 angle.
		// The dihedral angle is that along the third edge of the simplex.
		// All mixed partial derivatives are computed.
		// 
		// Input lower and upper bounds x,z on the lengths squared of
		// the edges.  The function also inputs sqrt(delta) 
		// and its first and second derivatives in
		// s, Ds, DDs.  The function returns a nonzero value if 
		// the calculation is a success.  The dihedral angle, and
		// its first and second derivatives are placed in h,Dh, and DDh.
		//
static int setDih3(const double x[6],const double z[6],
	const interval& s,const interval Ds[6],const interval DDs[6][6],
	interval& h, interval Dh[6],interval DDh[6][6]);

		//////////
		// Compute interval bounds on the second derivative of the
		// rhazim of a simplex.  To call this procedure, it is
		// necessary first to have computed dih and its first
		// and second partials. 
static int setRhazim(double x,double z,
	const interval& d,const interval Dd[6],const interval DDd[6][6],
	      interval DDc[6][6]);

		//////////
		// Compute interval bounds on the second derivative of the
		// rhazim2 of a simplex.  To call this procedure, it is
		// necessary first to have computed dih2 and its first
		// and second partials. 
static int setRhazim2(double x,double z,
	const interval& d,const interval Dd[6],const interval DDd[6][6],
	      interval DDc[6][6]);

		//////////
		// Compute interval bounds on the second derivative of the
		// rhazim3 of a simplex.  To call this procedure, it is
		// necessary first to have computed dih3 and its first
		// and second partials. 
static int setRhazim3(double x,double z,
	const interval& d,const interval Dd[6],const interval DDd[6][6],
	      interval DDc[6][6]);

		//////////
		// Compute interval bounds on the second derivative of the
		// solid angle of a simplex.  To call this procedure, it is
		// necessary first to have computed sqrt(delta) and its first
		// and second partials. 
		// 
		// Input x,z lower and upper bounds on the squares of the lengths
		// of the edges.
		// Input ss,Ds,DDs, the derivative information for sqrt(delta).
		// If the calculation is successful, a nonzero value is returned.
		// When the call is successful, 
		// the bounds on the second partials of the solid angle are
		// placed into the array DDx
		//
static int setSolid(const double x[6],const double z[6],
	const interval ss,const interval Ds[6],const interval DDs[6][6],
	interval DDx[6][6]);

		//////////
		// Compute interval bounds on the value, derivatives, 
		// and second derivatives of
		// the function sqrt(delta).
		// The lower and upper values of the domain are passed in
		// the arrays x and z.  As usual, these represent the
		// lengths squared of the variables.
		//
		// If the values are successfully computed a nonzero
		// value is returned, and the information is placed in
		// sqrt_d, Dsqrt_d, and DDsqrt_d.
		//
		// If the return is 0, the values of sqrt_d, Dsqrt_d, and
		// DDsqrt_d is undefined.
		//
static int setSqrtDelta(const double x[6],const double z[6],
	interval& sqrt_d,interval Dsqrt_d[6],interval DDsqrt_d[6][6]);

		//////////
		// Compute the interval bounds on the second derivatives of
		// the function vorAnalytic.
		// The lower and upper values of the domain are passes in
		// the arrays x and z.  As usual, these represent the 
		// lengths squared of the variables.
		//
		// If the bounds are computed, the return value is nonzero,
		// and the bounds are returned in DD.  If the return value
		// is zero, the values of the array DD are undefined.
		//
static int setVorAnalytic(const double x[6],const double z[6],
    double DD[6][6]);

		//////////
		// chi^2/(4 u delta)+ eta^2 126 is the circumradius squared of a simplex.
		// Compute interval bounds on the second derivatives of
		// chi^2/(4 u delta).
		// The lower and upper values of the domain are passed in
		// the arrays x and z. As usual, these represent the lengths
		// squared of the variables.
		//
		// If the values are successfully computed a nonzero
        // value is returned, and the information is placed in DDf.
		// Otherwise the value of DDf is undefined.
		//
static int setChi2over4uDelta(const double x[6],const double z[6],double DDf[6][6]);


	//////////
	// Check the correctness of secondDerive routines
	//
static void selfTest();

};


#endif
