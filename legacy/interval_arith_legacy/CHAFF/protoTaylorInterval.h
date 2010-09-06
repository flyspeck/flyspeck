#include "lineInterval.h"

class taylorInterval //: public lineInterval 
{ 
public:
	double upperBound();
	double lowerBound();
	double upperPartialBound(int);
	double lowerPartialBound(int);
};

class details;
class basisFunction;

class taylorFunction 
{
public: // private:
	details* X;

public:
	void add(const taylorFunction&);
	static void scale(taylorFunction&,double) ;
	int getReducibleState();
	void setReducibleState(int);
	int getOrderOfDifferentiability();
	taylorFunction(int capacity =0);
	taylorFunction(basisFunction&);
	~taylorFunction();
	double evalf();
};

class taylorSimplex
{
public:
	static const taylorFunction scalar,x1,x2,x3,x4,x5,x6,
		y1,y2,y3,y4,y5,y6,
		dih,dih2,dih3,sol,
		vorVc,vorSqc,vor, 
		// vorVc & vorSqc generate errors if a height > 2*trunc.
		anchoredvorVc; // use instead of vorVc on anc. simplices.

	// functions on an upright,flat,or quasiregular:
	// circumradius squared of the four faces of a simplex:
	static const taylorFunction eta2_126,eta2_135,eta2_234,eta2_456;
	};

class taylorQrtet
{
public:
	static const taylorFunction dih,dih2,dih3,
	   sol,rad2,
	   gamma,gamma1,gamma32,
	   vor,vor1,vor32;
};

class taylorFlat
{
public:
	// flat quarters (x4 is the diagonal).
	static const taylorFunction gamma,vor,sol,dih,dih2,dih3;
};

class taylorUpright
{
public:
	// upright quarter (x1 is the diagonal).
	static const taylorFunction gamma,vor,vorVc,sol,dih,dih2,dih3;
	static const taylorFunction swap_vor, swap_vorVc;
};

