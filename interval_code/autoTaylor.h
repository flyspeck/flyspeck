/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 2012-f-31                                                    */
/* ========================================================================== */

// Branched off from taylorData.h.
// Break into 2 files. Autogenerated piece and hand coded.

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
#include "univariate.h"

using namespace std;
using namespace tr1;


#ifndef autoTaylor_
#define autoTaylor_




/*
CLASS
	taylorData

	An interval-based linear approximation	with explicit error bounds.

OVERVIEW TEXT

	A taylorData is a souped-up version of lineInterval, which
	in turn is an enhancement of interval.  A taylorData is
	an interval version of a linear approximation to a function with
	explicit bounds on the error term.
	
	Because error terms on the second derivatives are included, 
	explicit lower and upper bounds, as well as bounds on the
	derivatives can be determined.

	A taylorData may contain invalid data.
	Bad data throws an "unstable" exception.

AUTHOR
	
	Thomas C. Hales
*/

class taylorData
{
public/* (for the moment) */:
  double DD[6][6];  // DD bounds on the abs. value of second partials.
  domain w; // w[] are upper bounds on widths.
  lineInterval tangentVector;
  //int validDataFlag;
  static taylorData plus
    (const taylorData&,const taylorData&);
  static taylorData scale
    (const taylorData& t1,const interval& c);

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
taylorData(const lineInterval&, const domain&,
        const double [6][6]);

	//////////
        // zero function of arbitrary width.
        //
taylorData(domain w0);

taylorData() {}; // dangerous.  Gives uninitialized values.

	//////////
	// A rigorous upper bound on the combined value of two simplices
	// sharing edges 2,3,4.  In general this bound will be better
	// than combining the bounds for the two separate simplices.
	// 
static double upperboundQ
    (const taylorData& cA,const taylorData& cB);

	//////////
	// A rigorous lower bound on the combined value of two simplices
	// sharing edges 2,3,4.  In general this bound will be better
	// than combining the bounds for the two separate simplices.
	// 
static double lowerboundQ
    (const taylorData& cA,const taylorData& cB);


};

//class details;

class primitive {

 public:
  virtual lineInterval tangentAtEstimate(const domain& x) const =0;

  virtual taylorData evalf4(const domain& w,const domain& x,
		const domain& y,const domain& z) const =0;
};


//typedef primitive* primPtr;


/*
CLASS
	Function

	A function that when evaluated yields a taylorData, that
	is it can be evaluated to give an explicit linear approximation
	with error bounds.

OVERVIEW TEXT

	 functions are the most important class in the the Kepler
	package in many ways.   They should be thought of as a rigorously
	implemented math library function.  To evaluate a function is
	to supply it with bounds on the lower and upper bounds on each
	of the variables, and an approximate center point where the
	taylor series approximation is to be computed.  

	When evaluated, instead of
	returning a mere double, a Function returns a taylorData,
	which constains information about the upper and lower bounds of
	the function on the given domain, and also about the upper and
	lower bounds of the derivatives of the function on the given domain.

	 functions can be added together and multiplied by scalars.
	To get an upper bound on the sum of two Functions it is
	better to add them and then evaluate the sum, rather than evaluate
	the individual functions and then add the results.  The reason
	for this is that there can be cancellation of terms, so that
	the bound by adding first is, roughly speaking |x-x|, rather than |x|+|-x|.

AUTHOR
	
	Thomas C. Hales
*/

typedef tr1::unordered_map<void*,interval> mapPrim;

class Function 
{
private:
  //int reduState;
public: 
	mapPrim data;

public:

	//////////
	// Add a Functions to a given one.
	//
Function operator+(const Function&) const;

	//////////
	// Scale a Function by a interval multiple.
	//
Function operator*(const interval&) const;

/*
	//////////
	// Compose Functions f (p1(x),...,f (p6(x))), where x=x1,...,x6.
	// Arguments are (f,p1,p2,...,p6).
        //
 Function composite(const Function&,
      const Function&,const Function&,const Function&,
      const Function&,const Function&,const Function&) const;
*/

	//////////
	// Functions are built up from certain primitive functions.
	// This is the constructor that converts a primitive function to
	// a Function.
	//
        //
Function(void* p);

	//////////
	// create a bitwise copy of a Function
	//
Function(const Function&);

	//////////
	// assignment of a Function
	//
Function& operator=(const Function& f);

	//////////
	// Deallocate memory:
	//
~Function();

	//////////
	// compose a univariate with a  function, f o g
	//
 static Function uni_compose(const univariate&,const Function&);

	//////////
	// multiply two  functions
	//
 static Function product(const Function&,const Function&);

	//////////
	// compose  functions f(x1,x2,x3,x4,x5,x6);
	//
 static Function compose
    (const Function&,
     const Function&, const Function&,const Function&,
     const Function&,const Function&,const Function&);

	//////////
	// reorder args f(x2,x3,x1,x5,x6,x2);
	//
 static Function rotate2(const Function&);

	//////////
	// reorder args f(x3,x1,x2,x6,x2,x5), etc.
	//
 static Function rotate3(const Function&);
 static Function rotate4(const Function&);
 static Function rotate5(const Function&);
 static Function rotate6(const Function&);


	//////////
	// Evaluate a Function
	// There are two arguments, x = lower bounds on variables,
	// z = upper bounds on variables,
	//
taylorData evalf(const domain& x,const domain& z) const;

	//////////
	// Evaluate a Function
        // precondition: The domain is x--z.
        // precondition: y is some point in the domain.
        // precondition for each i,  max(y[i]-x[i],z[i]-y[i]) <= w[i].
        // postcondition: The evaluation is at point y in the domain. 
        // post: 2nd derivative bounds hold on x--z.
	//

 taylorData evalf4(const domain& w,const domain& x,
		       const domain& y,const domain& z) const;

	//////////
	// Estimate a Function at a single point x.  Used in heuristics in recurse.cc
	// 
lineInterval tangentAtEstimate(const domain&) const;

	//////////
	//
//int getReducibleState() const;

	//////////
	//
//void setReducibleState(int);

	//////////
	// non-zero if its calculation involves division by Delta
        // 
//int hasDeltaDenom() const;

	//////////
	// Check the correctness of  routines.
	//
static void selfTest();

};


/*
CLASS
	taylorLibrary

	A library of static functions of six variables.

OVERVIEW TEXT

	This class contains the most important Functions for
	sphere packings.  Much more general functions can be built
	up by taking linear combinations of these, using the operator
	overloading on addition and scalar multiplication for
	Functions.

AUTHOR
	
	Thomas C. Hales
*/


class taylorLibrary
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
	static const Function unit,x1,x2,x3,x4,x5,x6,
		y1,y2,y3,y4,y5,y6,
	  delta,delta_x4,x1_delta_x,delta4_squared_x,vol_x,sol,rad2,

	  /*
	  dih,dih2,dih3,dih4,dih5,dih6,
	  ldih_x,ldih2_x,ldih3_x,ldih5_x,ldih6_x,

	  eulerA_x,

	  rhazim,rhazim2,rhazim3,
	  gchi1_x,gchi2_x,gchi3_x,gchi4_x,gchi5_x,gchi6_x,
	  x1cube,x1square,
	  num1,num2,num_combo1,
	  rat1,rat2,den2,
	  edge_flat2_x,
	  edge_flat_x,
	  flat_term_x,
	  taum_x,
	  halfbump_x1, halfbump_x4;
	  */

#endif
