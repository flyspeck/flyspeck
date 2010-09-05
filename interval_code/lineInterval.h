/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* ========================================================================== */

//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

#ifndef LINEINTERVAL_H
#define LINEINTERVAL_H

#include "interval.h"

/*
CLASS
	lineInterval

	A lineInterval is an interval version of a linear approximation to a 
	function.  Many of the functions in the Kepler library return
	lineIntervals.

OVERVIEW TEXT
	A lineInterval should be thought of as an interval version of a 
	linear function.
	Functions in the Kepler library typically return lineIntervals.
	This return value is a linearization of the function at the point
	at which it is evaluated.
	Upper and lower bounds on the function value are
	obtained through the member functions hi() and low().  Interval
	bounds on the partial derivatives of the lineInterval are obtained
	through the function partial(int).


AUTHOR
	Thomas C. Hales
*/

class lineInterval 
{ 
public: 
		interval f,Df[6];
public:
		//////////
		// The upper bound on a lineInterval
		//
inline double hi() const;
		
		//////////
		// The lower bound on a lineInterval
		//
inline double low() const;

		//////////
		// Interval bounds on the ith partial derivative of the lineInterval
		//
interval partial(int i) const;

		//////////
		// An interval can be promoted to a constant function (all
		// partial derivatives are zero)
		//
lineInterval(interval);

		//////////
		// Initialize to zero.
		//
lineInterval();
};


/*
CLASS
	domain

	Six doubles representing the squares of the edge lengths
	of a simplex.

AUTHOR
	Thomas C. Hales

*/
class domain 
{
private: 
	double x[6];

public:
	//////////
	// 
inline double getValue(int i) const;

	//////////
	// 
domain(double,double,double,double,double,double);

	//////////
	//
domain(const double x[6]);

	//////////
	//
static domain lowerD(const interval x[6]);

	//////////
	//
static domain upperD(const interval z[6]);

	//////////
	//
domain();
};

/*
CLASS 
	linearization

	A class of static functions defined on a simplex in three
	dimensions that return a lineInterval

OVERVIEW TEXT
The class linearization contains a number of static functions that return
a lineInterval.  The functions are defined on a simplex in three dimensions. 
Most of these functions are described in
the paper Sphere Packings I.  References to this paper will appear
as SP I.X in the documentation that follows.

There is one potential source of serious errors with these
routines.  The domain is given as a function of the <EMP>squares</EMP> of
the edges of the simplex.  The reason for this is that most of
the functions that arise are more naturally expressed in terms
of the squares of the edge lengths. (In Sphere Packings, I, the
unsquared coordinates are y1,...,y6, and the squared coordinates
are x1,...,x6.  These functions are always in terms of the 
	variables x1,...,x6.)

	The partial derivative information in the returned lineInterval is
	always with respect to the squared coordinates.

AUTHOR
	Thomas C. Hales

*/

class linearization 
{
public:

	//////////
	// The volume of a simplex is sqrt(delta)/12.  This may be used as
	// a definition of the polynomial delta.  Reference SP I.8.1.
	//
static lineInterval delta(const domain&);

	//////////
	// The dihedral angle of a simplex along the first edge.  
	// Explicit formulas for this function appear in SP I.8.3.1.
	// The edge numbering conventions are given in SP I.1.
	//
static lineInterval dih(const domain&);

	//////////
	// The dihedral angle of a simplex along the second edge.  
	// Explicit formulas for this function appear in SP I.8.3.1.
	// The edge numbering conventions are given in SP I.1.
	//
static lineInterval dih2(const domain&);

	//////////
	// The dihedral angle of a simplex along the third edge.  
	// Explicit formulas for this function appear in SP I.8.3.1.
	// The edge numbering conventions are given in SP I.1.
	//
static lineInterval dih3(const domain&);

	//////////
	// The dihedral angle of a simplex along the fourth edge.  
	// Explicit formulas for this function appear in SP I.8.3.1.
	// The edge numbering conventions are given in SP I.1.
	//
static lineInterval dih4(const domain&);

	//////////
	// The dihedral angle of a simplex along the fifth edge.  
	// Explicit formulas for this function appear in SP I.8.3.1.
	// The edge numbering conventions are given in SP I.1.
	//
static lineInterval dih5(const domain&);

	//////////
	// The dihedral angle of a simplex along the sixth edge.  
	// Explicit formulas for this function appear in SP I.8.3.1.
	// The edge numbering conventions are given in SP I.1.
	//
static lineInterval dih6(const domain&);

	//////////
	// The rhazim function of a simplex along the nth edge.  
	// Explicit formulas appear in general/sphere.hl
	//
static lineInterval rhazim(const domain&);

	//////////
	// The rhazim function of a simplex along the nth edge.  
	// Explicit formulas appear in general/sphere.hl
	//
static lineInterval rhazim2(const domain&);

	//////////
	// The rhazim function of a simplex along the nth edge.  
	// Explicit formulas appear in general/sphere.hl
	//
static lineInterval rhazim3(const domain&);

	//////////
	// The rhazim function of a simplex along the nth edge.  
	// Explicit formulas appear in general/sphere.hl
	//
static lineInterval rhazim4(const domain&);

	//////////
	// The rhazim function of a simplex along the nth edge.  
	// Explicit formulas appear in general/sphere.hl
	//
static lineInterval rhazim5(const domain&);

	//////////
	// The rhazim function of a simplex along the nth edge.  
	// Explicit formulas appear in general/sphere.hl
	//
static lineInterval rhazim6(const domain&);

	//////////
	// The solid angle of a simplex at its distinguished vertex.
	// Explicit formulas for this function appear in SP I.8.4.
	//
static lineInterval solid(const domain&);

	//////////
	// The circumradius squared of the face along edges 1,2,6 of a simplex.
	// Explicit formulas for this function appear in SP I.8.2.
	// The variables are the lengths squared of the edges of the triangle.
	//
static lineInterval eta2(const domain&);

	//////////
	// The circumradius squared of the face along edges 1,3,5 of a simplex.
	// Explicit formulas for this function appear in SP I.8.2.
	// The variables are the lengths squared of the edges of the triangle.
	//
static lineInterval eta2_135(const domain&);

	//////////
	// The circumradius squared of the face along edges 2,3,4 of a simplex.
	// Explicit formulas for this function appear in SP I.8.2.
	// The variables are the lengths squared of the edges of the triangle.
	//
static lineInterval eta2_234(const domain&);

	//////////
	// The circumradius squared of the face along edges 4,5,6 of a simplex.
	// Explicit formulas for this function appear in SP I.8.2.
	// The variables are the lengths squared of the edges of the triangle.
	//
static lineInterval eta2_456(const domain&);

	//////////
	// The circumradius squared of a simplex.
	// Explicit formulas for this function appear in SP I.8.2.
	//
static lineInterval rad2(const domain&); 

	//////////
	// The circumradius squared of a simplex minus the
	// circumradius squared of eta_126.
	// Explicit formulas for this function appear in SP I.8.2.
	// It is chi126^2/(4 u126 delta).
static lineInterval chi126squaredOverEtc(const domain& x);

	//////////
	// The analytic voronoi function.
	// Explicit formulas for this function appear in SP I.8.6.3.
	// The original domain of the function is the set of all simplices
	// with edges of length in the interval [2,sqrt(8)], such that
	// the simplex contains its own circumcenter.  This function is
	// analytically continued using the formula of SP I.8.6.3.
	//
static lineInterval vorAnalytic(const domain&);

	//////////
	// The function chi determinining the orientation of simplices,
	// where orientation is used in the sense of SP I.8.2.3.
	// Explicit formulas for this function appear in SP I.8.2.
	//
static lineInterval chi324(const domain&);

	//////////
	// Check the correctness of the linearization procedures.
	//
static void selfTest();

};


/*
CLASS 
	edgeBound

	A class of miscellaneous static functions.

OVERVIEW TEXT

	edgeBound contains a few functions that did not belong
	anywhere else.

AUTHOR
	Thomas C. Hales

*/

class edgeBound 
{
public:

	//////////
	// Computes the Maximum of the shorter
	// diagonal if possible, assuming that the shorter diagonal is
	// the one joining the two simplices A and B.
	// There are two simplices 
	//   A = (x0min,x1,x2,x3,x4,x5), B=(x0pmin,x1,x2,x3,x4p,x5p);
	// They share vertices x1,x2,x3;
	// Assume edge3 is the shorter diagonal.  Compute an upper bound
	// on this shorter diagonal.
	// We assume that the edge length belongs to [x3min,x3max(inputvalue)]
	// A revised x3max(output) is set, with x3max(output)<=x3max(input).
	//
static int shortDiagMax
	(double x0min,double x0pmin,double x1,double x2,double x3min,
        double& x3max,double x4,double x4p,double x5,double x5p);

	//////////
	// Given two simplices S (domain), and S' sharing the
	// second,third, and fourth edges with S.  
	// Assume S'=S(y1prime,y2(S),y3(S),y4(S),2,2).
	// Assume that dih2(S)+dih2(S') <pi and
	//             dih3(S)+dih3(S') <pi.
	// Return as maxCD 
	// if possible an upper bound on the crossdiagonal of (S,S').
	// The initial value of maxCD is ignored.
	//
static int crossDiagMax(const domain&,double y1prime,double& maxCD);

	//////////
	// given upper bound theta on dih, find corresponding upper bd on x4.
	//
static int x4_upper_from_dih_upper(const double x[6],const double z[6],
		double dih_upper, double& new_x4_upper);

	//////////
	// lower bound on chi234. This has only been implemented
	// when the face(2,3,4) is acute.
	// 
static double chi234min(const domain&, const domain&); // for acute guys only

};






#include "lineInterval_inline.h"

#endif
