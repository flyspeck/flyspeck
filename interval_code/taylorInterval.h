// copyright (c) 1997, Thomas C. Hales, all rights reserved.
#ifndef taylorInterval_
#define taylorInterval_
#include "lineInterval.h"


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

	A taylorInterval may contain invalid data, meaning that error
	bounds were impossible to obtain on the given domain.  Calling
	most of the functions will result in an error if the data is
	invalid.  To avoid the error messages, check the data with
	the member function isValidData().

AUTHOR
	
	Thomas C. Hales
*/

class taylorInterval
{
public/* (for the moment) */:
    double DD[6][6]; domain w; // w[] are upper bounds on widths.
    lineInterval centerPoint;
    int validDataFlag;
    static taylorInterval plus
		(const taylorInterval&,const taylorInterval&);
	static taylorInterval scale
		(const taylorInterval& t1,const interval& c);

public:

	//////////
	// Return a nonzero value if the data is valid, 0 otherwise.
	//
int isValidData() const;

	//////////
	// Taylor interval is a linear approximation at the center of
	// a cell with explicit error bounds.  center() is the
	// lineInterval giving the linear approximation at the center of the
	// cell.
	//
lineInterval center() const;

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
	// an an array [][] of doubles giving bounds on the second derivatives
	// the first argument is nonzero or zero depending on whether the
	// input is valid or not.
taylorInterval(int,const lineInterval&, const domain&,
        const double [6][6]);
taylorInterval() {};
};

class details;
class primitive;
typedef primitive* primPtr;


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

class taylorFunction 
{
private:
	int reduState;
public: // private:
	details* X;

public:

	//////////
	// Add a taylorFunctions to a given one.
	//
taylorFunction operator+(const taylorFunction&) const;

	//////////
	// Scale a taylorFunction by a interval multiple.
	//
taylorFunction operator*(const interval&) const;

	//////////
	// Constructor.  For advanced users: 
	// the capacity refers to the number of distinct
	// primitive functions occuring in the linear combination represented
	// by the taylorFunction.  If in doubt, 
	// use the default argument!
	//
taylorFunction(int capacity =0);

	//////////
	// taylorFunctions are built up from certain primitive functions.
	// This is the constructor that converts a primitive function to
	// a taylorFunction.
	// The class primitive and this class is only used in the implementation
	// details.  End-users can safely ignore this constructor.
	//
taylorFunction(primitive&);

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
	// Evaluate a taylorFunction at a single point x
	// 
lineInterval evalAt(const domain&) const;

	//////////
	//
int getReducibleState() const;

	//////////
	//
void setReducibleState(int);

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
	// lowVorVc is the voronoi function truncated at 1.255.
	// The domain is restricted to simplices whose first three edges
	// have heights 2.51.
	// highVorVc is the voronoi function truncated at 1.255.
	// The domain is restricted to simplices whose first edge is greater
	// than 2.51 and whose second and third edges are at most 2.51.
	// vorSqc is the voronoi function truncated at sqrt(2).
	// vor is the analytic voronoi function.
	//
	static const taylorFunction unit,x1,x2,x3,x4,x5,x6,
		y1,y2,y3,y4,y5,y6,
		dih,dih2,dih3,sol,
		lowVorVc,highVorVc,vorSqc,vor;

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


/*
CLASS
	taylorQrtet

	A library of static functions of a quasi-regular tetrahedron S

OVERVIEW TEXT

	This class contains functions defined on quasi-regular tetrahedra.
	Some of these functions are also available as functions on a
	general simplex in the class taylorSimplex.  The version here
	have been customized for quasi-regular tetrahedra.
	Much more general functions can be built
	up by taking linear combinations of these, using the operator
	overloading on addition and scalar multiplication for
	taylorFunctions.

AUTHOR
	
	Thomas C. Hales
*/

class taylorQrtet
{
public:
	//////////
	// dih,dih2,dih3 are the dihedral angles of a quasi-regular
	// tetrahedron along the first three edges.
	// sol is the solid angle,
	// gamma, gamma1,gamma32 are the functions
	// gamma - L zeta pt solid, where L = 0,1,3.2, respectively, and
	// gamma is the compression of the quasi-regular tetrahedron.
	// The functions vor, vor1, and vor32 are the
	// functions vor - L zetap pt solid, where L = 0,1,3.2, respectively,
	// and vor is the analytic voronoi function on the quasi-regular 
	// tetrahedron.
	// The function rad2 is the circumradius squared of a quasi-regular 
	// tetrahedrdon.
	// Also, quo is the quoin of a single Rogers simplex R=R(a,b,c),
	// a = y1/2, b=eta(y1,y2,y3), c = 1.255.
	//
	// The function rad2 has been designed to work on the slightly
	// bigger region yi<= 2 Sqrt[3] Tan[Pi/5], so it can be used in
	// connection with the dodecahedral conjecture.
	// 
	static const taylorFunction dih,dih2,dih3,
	   sol,rad2,
	   gamma,
	   vor,
	   quo;
};

/*
CLASS
	taylorFlat

	A library of static functions of a flat quarter S

OVERVIEW TEXT

	This class contains functions defined on flat quarters.
	Some of these functions are also available as functions on a
	general simplex in the class taylorSimplex.  The version here
	have been customized for flat quarters.
	Much more general functions can be built
	up by taking linear combinations of these, using the operator
	overloading on addition and scalar multiplication for
	taylorFunctions.  

	In these functions, the fourth edge is assumed to be the
	long edge.

AUTHOR
	
	Thomas C. Hales
*/

class taylorFlat
{
public:
	//////////
	// flat quarters (x4 is the diagonal).
	// gamma is the compression.
	// vor is the analytic voronoi function.
	// sol is the solid angle.
	// dih,dih2,dih3 are the dihedral angles along the first three edges.
	static const taylorFunction gamma,vor,vor1385,sol,dih,dih2,dih3;
};

/*
CLASS
	taylorUpright

	A library of static functions of an upright quarter S

OVERVIEW TEXT

	This class contains functions defined on upright quarters.
	Some of these functions are also available as functions on a
	general simplex in the class taylorSimplex.  The version here
	have been customized for upright quarters.
	Much more general functions can be built
	up by taking linear combinations of these, using the operator
	overloading on addition and scalar multiplication for
	taylorFunctions.  

	In these functions, the first edge is assumed to be the
	long edge.

AUTHOR
	
	Thomas C. Hales
*/

class taylorUpright
{
public:
	//////////
	// upright quarters (x1 is the diagonal).
	// gamma is the compression.
	// vor is the analytic voronoi function.
	// sol is the solid angle.
	// dih,dih2,dih3 are the dihedral angles along the first three edges.
	// vorVc is the voronoi function truncated at 1.255.
	// swapVor is the inverted analytic voronoi function, so that
	// octavor is (vor+swapVor)/2.
	// swapVorVc is the inverted truncated voronoi function at 1.255
	// so that octavor0 is (vorVc+swapVorVc)/2.
	//
	static const taylorFunction octavor,gamma,vor,vorVc,sol,dih,dih2,dih3;

	//////////
	// 
	static const taylorFunction swapVor, swapVorVc;
};

#endif
