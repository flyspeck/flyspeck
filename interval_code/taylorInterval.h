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


};

//class details;

class primitive {

 public:
  virtual lineInterval tangentAtEstimate(const domain& x) const =0;

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
  //int reduState;
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
taylorFunction(void* p);

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
	// compose a univariate with a Taylor function, f o g
	//
 static taylorFunction uni_compose(const univariate&,const taylorFunction&);

	//////////
	// multiply two Taylor functions
	//
 static taylorFunction product(const taylorFunction&,const taylorFunction&);

	//////////
	// compose Taylor functions f(x1,x2,x3,x4,x5,x6);
	//
 static taylorFunction compose
    (const taylorFunction&,
     const taylorFunction&, const taylorFunction&,const taylorFunction&,
     const taylorFunction&,const taylorFunction&,const taylorFunction&);

	//////////
	// reorder args f(x2,x3,x1,x5,x6,x2);
	//
 static taylorFunction rotate2(const taylorFunction&);

	//////////
	// reorder args f(x3,x1,x2,x6,x2,x5), etc.
	//
 static taylorFunction rotate3(const taylorFunction&);
 static taylorFunction rotate4(const taylorFunction&);
 static taylorFunction rotate5(const taylorFunction&);
 static taylorFunction rotate6(const taylorFunction&);


	//////////
	// Evaluate a taylorFunction
	// There are two arguments, x = lower bounds on variables,
	// z = upper bounds on variables,
	//
taylorInterval evalf(const domain& x,const domain& z) const;

	//////////
	// Evaluate a taylorFunction
        // precondition: The domain is x--z.
        // precondition: y is some point in the domain.
        // precondition for each i,  max(y[i]-x[i],z[i]-y[i]) <= w[i].
        // postcondition: The evaluation is at point y in the domain. 
        // post: 2nd derivative bounds hold on x--z.
	//

 taylorInterval evalf4(const domain& w,const domain& x,
		       const domain& y,const domain& z) const;

	//////////
	// Estimate a taylorFunction at a single point x.  Used in heuristics in recurse.cc
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
	  delta,delta_x4,x1_delta_x,delta4_squared_x,vol_x,sol,rad2,
	  dih,dih2,dih3,dih4,dih5,dih6,
	  ldih_x,ldih2_x,ldih3_x,ldih5_x,ldih6_x,
	  upper_dih,
	  eulerA_x,

	  rhazim,rhazim2,rhazim3,
	  gchi1_x,gchi2_x,gchi3_x,gchi4_x,gchi5_x,gchi6_x,
	  //	  marchalDih,marchalDih2,marchalDih3,
	  //    marchalDih4,marchalDih5,marchalDih6,
	  x1cube,x1square,
	  num1,num2,num_combo1,
	  rat1,rat2,den2,
	  edge_flat2_x,
	  edge_flat_x,
	  flat_term_x,
	  taum_x,
	  halfbump_x1, halfbump_x4;


	//////////
	// functions on an upright,flat,or quasiregular:
	// circumradius squared of the four faces of a simplex:
	// The circumradius squared of the face (ijk) of a simplex is eta2_ijk;
	// Miscellaneous functions.
	//
	static const taylorFunction eta2_126,eta2_135,eta2_234,eta2_456,
	  vol3_x_sqrt,
	  vol3f_x_lfun,
	  vol3f_x_sqrt2_lmplus,
	  arclength_x_123,
	  arclength_x_234,
	  arclength_x_126,
	  arclength_x_345,
	  norm2hhx,
	  asn797k,asnFnhk,lfun_y1,
	  acs_sqrt_x1_d4,	  acs_sqrt_x2_d4;

	static const taylorFunction
	  sol_euler_x_div_sqrtdelta,
	  sol_euler345_x_div_sqrtdelta,
	  sol_euler156_x_div_sqrtdelta,
	  sol_euler246_x_div_sqrtdelta,
	  dih_x_div_sqrtdelta_posbranch,
	  dih2_x_div_sqrtdelta_posbranch,
	  dih3_x_div_sqrtdelta_posbranch,
	  dih4_x_div_sqrtdelta_posbranch,
	  dih5_x_div_sqrtdelta_posbranch,
	  dih6_x_div_sqrtdelta_posbranch,
	  ldih_x_div_sqrtdelta_posbranch,
	  ldih2_x_div_sqrtdelta_posbranch,
	  ldih3_x_div_sqrtdelta_posbranch,
	  ldih4_x_div_sqrtdelta_posbranch,
	  ldih5_x_div_sqrtdelta_posbranch,
	  ldih6_x_div_sqrtdelta_posbranch,
	  surf_x,
	  vol3r_126_x,

	  dih_x_126_s2,
	  dih2_x_126_s2,
	  dih3_x_126_s2,
	  dih4_x_126_s2,
	  dih5_x_126_s2,
	  dih6_x_126_s2,
	  ldih_x_126_s2,
	  ldih2_x_126_s2,
	  ldih6_x_126_s2,
	  dih_x_135_s2,
	  dih2_x_135_s2,
	  dih3_x_135_s2,
	  dih4_x_135_s2,
	  dih5_x_135_s2,
	  dih6_x_135_s2,
	  ldih_x_135_s2,
	  ldih3_x_135_s2,
	  ldih5_x_135_s2,
	  lfun_sqrtx1_div2 ,

	  delta_x_135_s2,
	  delta_x_126_s2,

	  vol3_x_135_s2, 

	  gamma3f_x_vLR_lfun,
	  gamma3f_x_vLR0,
	  gamma3f_x_vL_lfun,  gamma3f_x_vL0,
	  gamma3f_x_v_lfun,  gamma3f_x_v0,


	  // dec 29 , 2010:

	  ldih_x_126_n,
	  ldih2_x_126_n,
	  ldih6_x_126_n,
	  ldih_x_135_n,
	  ldih3_x_135_n,
	  ldih5_x_135_n,

          gamma3f_126_x_s_n,
	  gamma3f_135_x_s_n,
	  gamma3f_vLR_x_nlfun,
	  gamma3f_vLR_x_n0,
	  gamma3f_vL_x_nlfun,
	  gamma3f_vL_x_n0,

	  // may 2011:
	  tau_lowform_x,
	  tau_residual_x,
	  delta_y_LC,
	  mdtau_y_LC,
	  mdtau2_y_LC,
	  euler_3flat_x,
	  euler_2flat_x,
	  euler_1flat_x,
	  taum_3flat_x,
	  taum_2flat_x,
	  taum_1flat_x,
	  delta_pent_x,
          ell_uvx, // sep 2011.
	  ell_vx2,


	  // mar 2012, local optimality of bcc lattice
	  selling_volume2,
	  selling_surface_nn,
	  selling_surface_nn2_013,
	  selling_surface_nn01_23,
	  selling_homog,
	  ;

	// construct x1^n1 .. x6^n6;
	static const taylorFunction monomial(int,int,int,int,int,int);

	static const taylorFunction taum_x1(const interval&,const interval&);
	static const taylorFunction taum_x2(const interval&,const interval&);
	static const taylorFunction taum_x1_x2(const interval&);

	static const taylorFunction arclength_x1(const interval&,const interval&);
	static const taylorFunction arclength_x2(const interval&,const interval&);

	static const taylorFunction surfR126d(const interval&);

	static const taylorFunction dih_template_B_x(const interval& x15,const interval& x45,
					const interval& x34,const interval& x12, 
					     const interval& x25);

	static const taylorFunction delta_template_B_x(const interval& x15,const interval& x45,
					const interval& x34,const interval& x12);


	static const taylorFunction /* taylorSimplex:: */ taum_template_B_x(const interval& x15,
								     const interval& x45,const interval& x34,const interval& x12   );

	static const taylorFunction /* taylorSimplex:: */ dih_hexall_x(const interval& x14, const interval& x12,
								const interval & x23);

	static const taylorFunction /* taylorSimplex:: */ dih1_hexall_x(const interval& x14, const interval& x12,
								const interval & x23);


	static const taylorFunction /* taylorSimplex:: */ upper_dih_hexall_x(const interval& x14, const interval& x12,
								const interval & x23);

	static const taylorFunction /* taylorSimplex:: */ delta_hexall_x(const interval& x14, const interval& x12,
								const interval & x23);

	static const taylorFunction /* taylorSimplex:: */ delta4_hexall_x(const interval& x14, const interval& x12,
								const interval & x23);


	static const taylorFunction /* taylorSimplex:: */ taum_hexall_x(const interval& x14, const interval& x12,
								const interval & x23);

	static const taylorFunction /* taylorSimplex:: */ eulerA_hexall_x(const interval& x14, const interval& x12,
								const interval & x23);

	static const taylorFunction /* taylorSimplex:: */ factor345_hexall_x(const interval& costheta);

	static const taylorFunction /* taylorSimplex:: */ law_cosines_234_x(const interval& costheta);

	static const taylorFunction /* taylorSimplex:: */ law_cosines_126_x(const interval& costheta);

	static const taylorFunction /* taylorSimplex:: */ lindih(const interval& theta);

	static const taylorFunction /* taylorSimplex:: */ delta_126_x(const interval& x3s, const interval& x4s, const interval& x5s);

	static const taylorFunction /* taylorSimplex:: */ delta_234_x(const interval& x1s, const interval& x5s, const interval& x6s);

	static const taylorFunction /* taylorSimplex:: */ delta_135_x(const interval& x2s, const interval& x4s, const interval& x6s);

	static const taylorFunction /* taylorSimplex:: */ taum_sub1_x(const interval& x1s);

	static const taylorFunction /* taylorSimplex:: */ delta_sub1_x(const interval& x1s);

	static const taylorFunction /* taylorSimplex:: */ taum_sub246_x(const interval& x2s,const interval& x4s,const interval& x6s);

	static const taylorFunction /* taylorSimplex:: */ taum_sub345_x(const interval& x3s,const interval& x4s,const interval& x5s);


};




#endif
