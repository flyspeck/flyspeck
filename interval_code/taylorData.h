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
#include "univariate.h"

using namespace std;
using namespace tr1;


#ifndef taylorData_
#define taylorData_




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
	// lineInterval giving the approximation at the expansion point of the
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

	A Function that when evaluated yields a taylorData, that
	is it can be evaluated to give an explicit linear approximation
	with error bounds.

OVERVIEW TEXT

	Functions are the most important class in the the Kepler
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

	Functions can be added together and multiplied by scalars.
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



 // Add a Function to a given one.
Function operator+(const Function&) const;

Function operator*(const interval&) const;

	//////////
	// Functions are built up from certain primitive functions.
	// This is the constructor that converts a primitive function to
	// a Function.
Function(void* p);

	// create a bitwise copy of a Function
Function(const Function&);

Function& operator=(const Function& f);

	// Deallocate memory:
~Function();
 
 //univariate at slot i=0..5 (note indexing)
 static Function uni_slot(const univariate&x, int slot);

// compose a univariate with a  function, f o g
 static Function uni_compose(const univariate&,const Function&);

 // constructor of a locally constant function: primitiveLC
 static Function mk_LC(interval (*)(const domain&,const domain& ));

// constructor from a line interval (cf. primitive A )
static Function mk_raw(lineInterval (*)(const domain& ),
		 int (*)(const domain& ,const domain&,double [6][6]));

// constructor from a monomial; primitive_monom.
static Function mk_monomial(const int m[6]); 

 static Function mk_monomial(int i1,int i2,int i3,int i4,int i5,int i6);

 static Function product(const Function&,const Function&);

	//////////
	// compose functions f(x1,x2,x3,x4,x5,x6);
 static Function compose
    (const Function&,
     const Function&, const Function&,const Function&,
     const Function&,const Function&,const Function&);

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
	// Estimate a Function at a single point x. 
        // Used in heuristics in recurse.cc
	// 
lineInterval tangentAtEstimate(const domain&) const;

	//////////
	// constant function taking value 1.
        // we put it here rather than in the library. It is needed early.
	//
 static const Function unit;

 static void selfTest();

};
#endif
