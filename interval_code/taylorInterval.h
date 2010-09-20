/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* ========================================================================== */

#include <iomanip>
#include <utility>
#include <tr1/unordered_map>
extern "C"
{
#include <math.h>
#include <time.h>
#include <stdlib.h>
#include <float.h>
}
#include "lineInterval.h"

using namespace std;
using namespace tr1;


#ifndef taylorInterval_
#define taylorInterval_




/*
CLASS
	taylorInterval

	An interval-based linear approximation	with explicit error bounds.

OVERVIEW TEXT

	A taylorInterval is a souped-up version of lineInterval, which
	in turn is an enhancement of interval.  A taylorInterval is
	an interval version of a linear approximation to a function with
	explicit bounds on the error term.
	
	Because error terms on the second derivatives are included, 
	explicit lower and upper bounds, as well as bounds on the
	derivatives can be determined.

	A taylorInterval may contain invalid data.
	Bad data throws an "unstable" exception.

AUTHOR
	
	Thomas C. Hales
*/

class taylorInterval
{
public/* (for the moment) */:
  double DD[6][6];  // DD bounds on the abs. value of second partials.
  domain w; // w[] are upper bounds on widths.
  lineInterval tangentVector;
  //int validDataFlag;
  static taylorInterval plus
    (const taylorInterval&,const taylorInterval&);
  static taylorInterval scale
    (const taylorInterval& t1,const interval& c);

public:

	//////////
	// Taylor interval is a linear approximation at the expansion point of
	// a cell with explicit error bounds.  tangentVectorOf() is the
	// lineInterval giving the linear approximation at the expansion point of the
	// cell.
	//
lineInterval tangentVectorOf() const;

	//////////
	// A rigorous upper bound on the value over the entire cell.
	//
double upperBound() const;

	//////////
	// A rigorous lower bound on the value over an entire cell.
	//
double lowerBound() const;

	//////////
	// A rigorous upper bound on the combined value of two simplices
	// sharing edges 2,3,4.  In general this bound will be better
	// than combining the bounds for the two separate simplices.
	// 
static double upperboundQ
    (const taylorInterval& cA,const taylorInterval& cB);

	//////////
	// A rigorous lower bound on the combined value of two simplices
	// sharing edges 2,3,4.  In general this bound will be better
	// than combining the bounds for the two separate simplices.
	// 
static double lowerboundQ
    (const taylorInterval& cA,const taylorInterval& cB);


	//////////
	// A rigorous upper bound on the ith partial derivative over the 
	// entire cell.
	//
double upperPartial(int) const;

	//////////
	// A rigorous lower bound on the ith partial deriviative over the
	// entire cell.
	//
double lowerPartial(int) const;

	//////////
	// A constructor, taking the lineInterval at the center,
	// a bound on the half-widths of the cell (domain&),
	// an an array [][] of doubles giving bounds on the absolute values of
        // second derivatives.
        //
taylorInterval(const lineInterval&, const domain&,
        const double [6][6]);

	//////////
        // zero function of arbitrary width.
        //
taylorInterval(domain w0);

taylorInterval() {}; // dangerous.  Gives uninitialized values.

};

//class details;

class primitive {

 public:
  virtual lineInterval tangentAt(const domain& x) const =0;

  virtual taylorInterval evalf4(const domain& w,const domain& x,
		const domain& y,const domain& z) const =0;
};


//typedef primitive* primPtr;


/*
CLASS
	taylorFunction

	A function that when evaluated yields a taylorInterval, that
	is it can be evaluated to give an explicit linear approximation
	with error bounds.

OVERVIEW TEXT

	Taylor functions are the most important class in the the Kepler
	package in many ways.   They should be thought of as a rigorously
	implemented math library function.  To evaluate a function is
	to supply it with bounds on the lower and upper bounds on each
	of the variables, and an approximate center point where the
	taylor series approximation is to be computed.  

	When evaluated, instead of
	returning a mere double, a taylorFunction returns a taylorInterval,
	which constains information about the upper and lower bounds of
	the function on the given domain, and also about the upper and
	lower bounds of the derivatives of the function on the given domain.

	Taylor functions can be added together and multiplied by scalars.
	To get an upper bound on the sum of two taylorFunctions it is
	better to add them and then evaluate the sum, rather than evaluate
	the individual functions and then add the results.  The reason
	for this is that there can be cancellation of terms, so that
	the bound by adding first is, roughly speaking |x-x|, rather than |x|+|-x|.

AUTHOR
	
	Thomas C. Hales
*/

typedef tr1::unordered_map<void*,interval> mapPrim;

class taylorFunction 
{
private:
	int reduState;
public: 
	mapPrim data;

public:

	//////////
	// Add a taylorFunctions to a given one.
	//
taylorFunction operator+(const taylorFunction&) const;

	//////////
	// Scale a taylorFunction by a interval multiple.
	//
taylorFunction operator*(const interval&) const;

/*
	//////////
	// Compose taylorFunctions f (p1(x),...,f (p6(x))), where x=x1,...,x6.
	// Arguments are (f,p1,p2,...,p6).
        //
 taylorFunction composite(const taylorFunction&,
      const taylorFunction&,const taylorFunction&,const taylorFunction&,
      const taylorFunction&,const taylorFunction&,const taylorFunction&) const;
*/

	//////////
	// taylorFunctions are built up from certain primitive functions.
	// This is the constructor that converts a primitive function to
	// a taylorFunction.
	//
        //
 taylorFunction::taylorFunction(void* p);

	//////////
	// create a bitwise copy of a taylorFunction
	//
taylorFunction(const taylorFunction&);

	//////////
	// assignment of a taylorFunction
	//
taylorFunction& operator=(const taylorFunction& f);

	//////////
	// Deallocate memory:
	//
~taylorFunction();

	//////////
	// Evaluate a taylorFunction
	// There are two arguments, x = lower bounds on variables,
	// z = upper bounds on variables,
	//
taylorInterval evalf(const domain& x,const domain& z) const;

	//////////
	// Evaluate a taylorFunction
        // precondition: The domain x--z is contained in the rectangle center y width w.
        // postcondition: The evaluation is at center y, 
        // post: 2nd derivative bounds hold on x--z.
	//

 taylorInterval evalf4(const domain& w,const domain& x,
		       const domain& y,const domain& z) const;


	//////////
	// Evaluate a taylorFunction at a single point x
	// 
lineInterval tangentAt(const domain&) const;

	//////////
	//
int getReducibleState() const;

	//////////
	//
void setReducibleState(int);

	//////////
	// non-zero if its calculation involves division by Delta
        // 
int hasDeltaDenom() const;

	//////////
	// Check the correctness of Taylor routines.
	//
static void selfTest();

};


/*
CLASS
	taylorSimplex

	A library of static functions of a simplex S

OVERVIEW TEXT

	This class contains the most important taylorFunctions for
	sphere packings.  Much more general functions can be built
	up by taking linear combinations of these, using the operator
	overloading on addition and scalar multiplication for
	taylorFunctions.

AUTHOR
	
	Thomas C. Hales
*/

class taylorSimplex
{
public:

	//////////
	// unit is the constant function taking value 1.
	// x1,..,x6 are the squares of the edge lengths.
	// y1,...y6 are the edge lengths.
	// dih,dih2,dih3, are the dihedral angles along the first
	// three edges.
	// sol is the solid angle of a simplex
        // all of these are expressed in terms of the variables xi.
	//
	static const taylorFunction unit,x1,x2,x3,x4,x5,x6,
		y1,y2,y3,y4,y5,y6,
	  delta,vol_x,sol,
	  dih,dih2,dih3,dih4,dih5,dih6,
	  rhazim,rhazim2,rhazim3,
	  gchi1_x,gchi2_x,gchi3_x,gchi4_x,gchi5_x,gchi6_x;

	//////////
	// functions on an upright,flat,or quasiregular:
	// circumradius squared of the four faces of a simplex:
	// The domain of eta2_126,eta2_135,eta2_234, and eta2_456 are simplices
	// whose edges are between 2.51 and 2sqrt(2), or 2 and 2.51 as appropriate.
	// The circumradius squared of the face (ijk) of a simplex is eta2_ijk;
	//
	// These functions take into account the slightly different edge
	// lengths occuring in the dodecahedral conjecture, and works
	// fine in that context as well.
	//
	static const taylorFunction eta2_126,eta2_135,eta2_234,eta2_456;
};


#endif
