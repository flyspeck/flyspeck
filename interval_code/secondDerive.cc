//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

// This and 3d.cc give essential bounds on the second derivatives
// of the key functions used in the Kepler conjecture.

// This file contains the six dimensional functions such as vorAnalytic,
// dih,solid, etc. and 3d.cc contains the three dimensional functions
// such as eta, and quoin.

// The regions over which the bounds were computed were flat quarters,
// upright quarters, and quasi-regular tetrahedra.  The output has
// been saved in several files out.sec.* and out.dih.*.

// This output will be fed into the inequality verifier to give good
// Taylor approximations to these functions.

// These programs only need to be run once, which is fortunate, because
// they take a few days each 


// compute second derivatives 

// we assume that multiplication by powers of two is exact,
// that unary negation is exact,
// and that u*v + (-x)*y gives correct upward rounding (but u*v- x*y does not).

#include <iomanip.h>
#include <iostream.h>
extern "C"
{
#include <math.h>
#include <stdlib.h>
#include <float.h>
#include <time.h>
}
#include "error.h"
#include "interval.h"
#include "secondDerive.h"


/*
CLASS
    Leibniz
 
    Some calculus methods including the product and quotient rules.
    The code is written for functions of 6 variables, but this could
    be easily modified.
 
OVERVIEW TEXT
    The class Leibniz contains
    some calculus methods including the product and quotient rules.
    It also contains a square root method that computes the derivatives
    of the square root of a function by the chain rule.
 
AUTHOR
    Thomas C. Hales
*/
 
class Leibniz
{
public:
 
        //////////
        // Use the product rule to compute a product uv, its first
        // derivatives Duv, and its second derivatives DDuv in terms
        // of the same data for u and v.
        //
        // The input is the derivative information for the first function
        // u, Du, and DDu, and for the second function v, Dv, DDv.
        //
        // void is returned because the calculation will always be
        // successful provided the magnitudes of the numbers involved
        // are less than <float.h>DBL_MAX
        //
        // It is assumed that the functions are functions of 6 variables.
        //
static void product(const interval& u,const interval Du[6],
    const interval DDu[6][6],
    const interval& v,const interval Dv[6],const interval DDv[6][6],
    interval& uv,interval Duv[6],interval DDuv[6][6]);
 
        //////////
        // Use the chain rule to compute the sqrt of a function, and
        // its first and second derivatives in terms of the same data
        // for the function
        //
        // The input is the value and derivative information of the
        // first function u, Du, DDu.
        // The return is sqrt_u, Dsqrt_u, DDsqrt_u containing the
        // square root information.
        //
        // If calculation is not sucessful, 0 is returned, otherwise
        // a nonzero is returned.  The squrt_u variables take undefined
        // values if the calculation is not a success.
        // This function should be safe to
        // call even if u is not strictly positive, but no useful
        // information will be obtained.
        //
        // It is assumed that the functions are functions of 6 variables.
        //
static int Dsqrt(const interval&u,const interval Du[6],const interval DDu[6][6],
   interval& sqrt_u,interval Dsqrt_u[6],interval DDsqrt_u[6][6]);
 
 
        //////////
        // Use the quotient rule to compute a quotient v=a/b, its first
        // derivatives Dv, and its second derivatives DDv in terms
        // of the same data for a and b.
        //
        // The input is the derivative information for the first function
        // a, Da, and DDa, and for the second function b, Db, DDb.
        //
        // If the computation is a sucess a nonzero integer is returned.
        // The usual cause of an unsuccesful call is a zero denominator.
        // An effort is made to avoid a division by zero.  If this appears
        // likely an unsucessful return is made.
        //
        // It is assumed that the functions are functions of 6 variables.
        //
static int quotient(const interval& a,const interval Da[6],
    const interval DDa[6][6],
    const interval& b,const interval Db[6],const interval DDb[6][6],
    interval& v,interval Dv[6],interval DDv[6][6]);
};
 


// pretty printing of intervals....
class band {
        public:
        double ymin;
        double ymax;
        friend ostream &operator<< (ostream &stream,band c);
        band(interval x) {ymin = interMath::inf(x); ymax = interMath::sup(x); }
        };

ostream &operator<< (ostream &stream,band c)
        {
        stream << "{" << c.ymin << "," << c.ymax << "}; ";
        return stream;
        }

static void print(interval f,const interval Df[6],const interval DDf[6][6])
	{
	int i,j;
	cout << "f = " << f << endl << "Df = ";
	for (i=0;i<6;i++) cout << Df[i]  << " ";
	cout << endl << "DDf = {";
	for (i=0;i<6;i++)
	{
	cout << "{";
	for (j=0;j<6;j++) cout << DDf[i][j].lo <<  (j<5? ",": " ") ;
	cout << "}" << (i<5 ?"," :"}") << endl;
	}
	cout << flush;
	}
 

static inline double max(double x,double y)
	{
	return (x > y ? x : y);
	}

static inline double min(double x,double y)
	{
	return (x > y ? y : x);
	}

static void array_multiply(interval a,const interval Df[6][6],
	interval aDf[6][6])
	{
	int i,j;
	if (interMath::inf(a) > 0.0)
		{
		interMath::up();
		for (i=0;i<6;i++) for (j=0;j<6;j++)
			(Df[i][j].hi < 0.0 ? aDf[i][j].hi = Df[i][j].hi*a.lo :
								 aDf[i][j].hi = Df[i][j].hi*a.hi);
		interMath::down();
		for (i=0;i<6;i++) for (j=0;j<6;j++)
			(Df[i][j].lo > 0.0 ? aDf[i][j].lo = Df[i][j].lo*a.lo :
								 aDf[i][j].lo = Df[i][j].lo*a.hi);
		}
	else if (interMath::sup(a) < 0.0)
		{
		interMath::up();
		for (i=0;i<6;i++) for (j=0;j<6;j++)
			(Df[i][j].lo < 0.0 ? aDf[i][j].hi = Df[i][j].lo*a.lo :
								 aDf[i][j].hi = Df[i][j].lo*a.hi);
		interMath::down();
		for (i=0;i<6;i++) for (j=0;j<6;j++)
			(Df[i][j].hi > 0.0 ? aDf[i][j].lo = Df[i][j].hi*a.lo:
								 aDf[i][j].lo = Df[i][j].hi*a.hi);
		}
	else    {
		interMath::up();
		for (i=0;i<6;i++) for (j=0;j<6;j++)
		if (Df[i][j].lo > 0.0) aDf[i][j].hi = Df[i][j].hi*a.hi;
		else if (Df[i][j].hi < 0.0) aDf[i][j].hi = Df[i][j].lo*a.lo;
		else aDf[i][j].hi = max(a.lo*Df[i][j].lo,a.hi*Df[i][j].hi);
 
		interMath::down();
		for (i=0;i<6;i++) for (j=0;j<6;j++)
		if (Df[i][j].lo > 0.0) aDf[i][j].lo = Df[i][j].hi*a.lo;
		else if (Df[i][j].hi < 0.0) aDf[i][j].lo = Df[i][j].lo*a.hi;
		else aDf[i][j].lo = min(a.lo*Df[i][j].hi,a.hi*Df[i][j].lo);
		}
        }

static void half_array_multiply(interval a,const interval Df[6][6],
	interval aDf[6][6])
	{
	int i,j;
	if (interMath::inf(a) > 0.0)
		{
		interMath::up();
		for (i=0;i<6;i++) for (j=i;j<6;j++)
				(Df[i][j].hi < 0.0 ? aDf[i][j].hi = Df[i][j].hi*a.lo :
									 aDf[i][j].hi = Df[i][j].hi*a.hi);
		interMath::down();
		for (i=0;i<6;i++) for (j=i;j<6;j++)
				(Df[i][j].lo > 0.0 ? aDf[i][j].lo = Df[i][j].lo*a.lo :
									 aDf[i][j].lo = Df[i][j].lo*a.hi);
		}
	else if (interMath::sup(a) < 0.0)
		{
		interMath::up();
		for (i=0;i<6;i++) for (j=i;j<6;j++)
				(Df[i][j].lo < 0.0 ? aDf[i][j].hi = Df[i][j].lo*a.lo :
									 aDf[i][j].hi = Df[i][j].lo*a.hi);
		interMath::down();
		for (i=0;i<6;i++) for (j=i;j<6;j++)
				(Df[i][j].hi > 0.0 ? aDf[i][j].lo = Df[i][j].hi*a.lo:
									 aDf[i][j].lo = Df[i][j].hi*a.hi);
		}
	else    {
		interMath::up();
		for (i=0;i<6;i++) for (j=i;j<6;j++)
		if (Df[i][j].lo > 0.0) aDf[i][j].hi = Df[i][j].hi*a.hi;
		else if (Df[i][j].hi < 0.0) aDf[i][j].hi = Df[i][j].lo*a.lo;
		else aDf[i][j].hi = max(a.lo*Df[i][j].lo,a.hi*Df[i][j].hi);
 
		interMath::down();
		for (i=0;i<6;i++) for (j=i;j<6;j++)
		if (Df[i][j].lo > 0.0) aDf[i][j].lo = Df[i][j].hi*a.lo;
		else if (Df[i][j].hi < 0.0) aDf[i][j].lo = Df[i][j].lo*a.hi;
		else aDf[i][j].lo = min(a.lo*Df[i][j].hi,a.hi*Df[i][j].lo);
		}
	}


/* We use the formula for each third of a Voronoi volume from I.8.6.3:
	[x1 (x2+x6-x1)+ x2(x1+x6-x2)] chi(x4,x5,x3,x1,x2,x6)/[
		48 u(x1,x2,x6) delta(x1,..x6)^0.5 ]
   Write this as a product a/b, a = f1 chi;  b = 48 u delta^0.5
*/



static void setF126(const double x[6],const double z[6],
	interval& f, interval Df[6], interval DDf[6][6])
	{
	double vmin, vmax, xmin[6], xmax[6];
	double xxmin[6][6], xxmax[6][6];
	double xa[6],za[6];
	int i,j;
 
	for (i=0;i<6;i++) for (j=0;j<6;j++) 
		{ xxmin[i][j]=0.0; xxmax[i][j]=0.0; }
	for (i=0;i<6;i++) { xmin[i]=0.0; xmax[i]=0.0; }
	xxmin[0][0]=xxmax[0][0]=xxmin[1][1]=xxmax[1][1]= -2.0;
	xxmin[0][1]=xxmax[0][1]=xxmin[1][0]=xxmax[1][0]=  2.0;
	xxmin[0][5]=xxmax[0][5]=xxmin[1][5]=xxmax[1][5]=  1.0;
	xxmin[5][0]=xxmax[5][0]=xxmin[5][1]=xxmax[5][1]=  1.0;
 
	interMath::down(); 
	xmin[0]=-2.0*z[0] + 2.0*x[1] + x[5];
	xmin[1]= 2.0*x[0] - 2.0*z[1] + x[5];
	xmin[5]= x[0]+x[1];
 
	interMath::up();
	xmax[0]= -2.0*x[0] + 2.0*z[1] + z[5];
	xmax[1]= 2.0*z[0] - 2.0*x[1] + z[5];
	xmax[5]= z[0]+z[1];
	
 
	// compute function max;
	for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
		if (xmin[i]>=0.0) xa[i]=za[i];
		else if (xmax[i]<=0.0) za[i]=xa[i];
		}
	// rounding mode is still up.
	vmax = 2.0*za[0]*za[1] + za[0]*za[5] + za[1]*za[5] 
		+ (-xa[0])*xa[0] + (-xa[1])*xa[1];
	for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
		if (xmin[i]>=0.0) za[i]=xa[i];
		else if (xmax[i]<=0.0) xa[i]=za[i];
		}
	interMath::down();
	vmin = 2.0*xa[0]*xa[1] + xa[0]*xa[5] + xa[1]*xa[5]
			+ (-za[0])*za[0] + (-za[1])*za[1];
 
	f = interval(vmin,vmax);
	for (i=0;i<6;i++) Df[i]=interval(xmin[i],xmax[i]);
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		DDf[i][j]=interval(xxmin[i][j],xxmax[i][j]);
	
	}



static void setChi126(const double x[6],const double z[6],
	interval& f,interval Df[6],interval DDf[6][6])
	{
	double vmin, vmax, xmin[6], xmax[6], xxmin[6][6], xxmax[6][6];
	double xa[6],za[6];
	int i,j;
	for (i=2;i<6;i++) for (j=0;j<6;j++) xxmin[i][j]=xxmax[i][j]=0.0;
	     //^ 2 here because others are initialized.
 
	interMath::down();
	xxmin[0][0]= -2.0*z[3]; 
	xxmin[0][1]= x[3]+x[4]-2.0*z[5]; 
	xxmin[0][2]= x[5]; 
	xxmin[0][3]= -2.0*z[0]+x[1]+x[5]; 
	xxmin[0][4]= x[1]; 
	xxmin[0][5]= -2.0*z[1] + x[2]+x[3]; 
	
	xxmin[1][1]= -2.0*z[4]; 
	xxmin[1][2]= x[5]; 
	xxmin[1][3]= x[0]; 
	xxmin[1][4]= x[0]- 2.0*z[1] + x[5]; 
	xxmin[1][5]= -2.0*z[0] +x[2]+x[4]; 
 
	xxmin[2][5]= x[0]+x[1]-2.0*z[5]; 
	xxmin[3][5]= x[0]; 
	xxmin[4][5]= x[1]; 
	xxmin[5][5]= -2.0*z[2]; 
 
	interMath::up();
	xxmax[0][0]= -2.0*x[3];
	xxmax[0][1]= z[3]+z[4]-2.0*x[5];
	xxmax[0][2]= z[5];
	xxmax[0][3]= -2.0*x[0]+z[1]+z[5];
	xxmax[0][4]= z[1];
	xxmax[0][5]=-2.0*x[1]+z[2]+z[3];
 
	xxmax[1][1]= -2.0*x[4];
	xxmax[1][2]= z[5];
	xxmax[1][3]= z[0];
	xxmax[1][4]= z[0]- 2.0*x[1] + z[5];
	xxmax[1][5] = -2.0*x[0]+z[2]+z[4];
 
	xxmax[2][5]=z[0]+z[1]-2.0*x[5];
	xxmax[3][5]= z[0];
	xxmax[4][5]=z[1];
	xxmax[5][5]=-2.0*x[2];
 
	for (i=0;i<6;i++) for (j=0;j<i;j++) 
		{ xxmin[i][j]=xxmin[j][i]; xxmax[i][j]=xxmax[j][i]; }
 
	// now for xmax[j]
	interMath::up();
	for (j=0;j<6;j++)
	{
		for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
			if (xxmin[j][i]>=0.0) xa[i]=za[i];
			else if (xxmax[j][i]<=0.0) za[i]=xa[i];
			}
		switch (j) 
		  {
		  case 0: xmax[j]= 2.0*(-xa[0])*xa[3]+ za[1]*za[3]+za[1]*za[4]
				+ 2.0*(-xa[1])*xa[5] + za[2]*za[5]+za[3]*za[5];
				break;
		  case 1: xmax[j]= za[0]*za[3]+za[0]*za[4]+2.0*(-xa[1])*xa[4]
				+2.0*(-xa[0])*xa[5]+za[2]*za[5]+za[4]*za[5];
				break;
		  case 2: xmax[j]= za[0]*za[5]+za[1]*za[5]+(-xa[5])*xa[5];
				break;
		  case 3: xmax[j]= xa[0]*(-xa[0])+za[0]*za[1]+za[0]*za[5];
				break;
		  case 4: xmax[j]= za[0]*za[1]+(-xa[1])*xa[1]+za[1]*za[5];
				break;
		  case 5: xmax[j]= 2.0*(-xa[0])*xa[1]+za[0]*za[2]+za[1]*za[2]
				+za[0]*za[3]+za[1]*za[4]+2.0*(-xa[2])*xa[5];
				break;
		  }
	}
 
	interMath::down();
	// now for xmin[j]
	for (j=0;j<6;j++)
	{
		for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
			if (xxmin[j][i]>=0.0) za[i]=xa[i];
			else if (xxmax[j][i]<=0.0) xa[i]=za[i];
			}
		switch (j) 
		  {
		  case 0: xmin[j]= 2.0*(-za[0])*za[3] + xa[1]*xa[3]+xa[1]*xa[4]
				+2.0*((-za[1])*za[5]) + xa[2]*xa[5]+xa[3]*xa[5];
				break;
		  case 1: xmin[j]= xa[0]*xa[3]+xa[0]*xa[4]+2.0*(-za[1])*za[4]
				+2.0*(-za[0])*za[5]+xa[2]*xa[5]+xa[4]*xa[5];
				break;
		  case 2: xmin[j]= xa[0]*xa[5]+xa[1]*xa[5]+(-za[5])*za[5];
				break;
		  case 3: xmin[j]= za[0]*(-za[0])+xa[0]*xa[1]+xa[0]*xa[5];
				break;
		  case 4: xmin[j]= xa[0]*xa[1]+(-za[1])*za[1]+xa[1]*xa[5];
				break;
		  case 5: xmin[j]= 2.0*(-za[0])*za[1]+xa[0]*xa[2]+xa[1]*xa[2]
				+xa[0]*xa[3]+xa[1]*xa[4]+2.0*(-za[2])*za[5];
				break;
		  }
	}
	// now for vmax
	interMath::up();
	for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
		if (xmin[i]>=0.0) xa[i]=za[i];
		else if (xmax[i]<=0.0) za[i]=xa[i];
		}
	vmax = (xa[0]*(-xa[0]))*xa[3]+za[0]*za[1]*za[3]+za[0]*za[1]*za[4]
		+ ((-xa[1])*xa[1])*xa[4]+2.0*((-xa[0])*xa[1])*xa[5]+za[0]*za[2]*za[5]
		+ za[1]*za[2]*za[5]+za[0]*za[3]*za[5]+za[1]*za[4]*za[5]
		+((-xa[2])*xa[5])*xa[5];
 
	interMath::down();	
	for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
		if (xmin[i]>=0.0) za[i]=xa[i];
		else if (xmax[i]<=0.0) xa[i]=za[i];
		}
 
	vmin = za[0]*((-za[0])*za[3])+xa[0]*xa[1]*xa[3]+xa[0]*xa[1]*xa[4]
		+((-za[1])*za[1])*za[4]+2.0*((-za[0])*za[1])*za[5]
		+xa[0]*xa[2]*xa[5]
		+ xa[1]*xa[2]*xa[5]+xa[0]*xa[3]*xa[5]+xa[1]*xa[4]*xa[5]
		+((-za[2])*za[5])*za[5];
 
	f = interval(vmin,vmax);
	for (i=0;i<6;i++) Df[i]=interval(xmin[i],xmax[i]);
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		DDf[i][j]=interval(xxmin[i][j],xxmax[i][j]);
	
	} // end of setChi126;

int secondDerive::setChi126(const double x[6],const double z[6],interval DDf[6][6])
	{
	interval f,Df[6];
	::setChi126(x,z,f,Df,DDf);
	return 1;
	}

static void setU126(const double x[6],const double z[6],
	interval& f, interval Df[6], interval DDf[6][6])
	{
	double vmin, vmax, xmin[6], xmax[6], xxmin[6][6], xxmax[6][6];
	double xa[6],za[6];
	int i,j;
 
	for (i=0;i<6;i++) for (j=0;j<6;j++) 
		{ xxmin[i][j]=0.0; xxmax[i][j]=0.0; }
	for (i=0;i<6;i++) { xmin[i]=0.0; xmax[i]=0.0; }
	xxmin[0][0]=xxmax[0][0]=xxmin[1][1]=xxmax[1][1]= -2.0;
	xxmin[5][5]=xxmax[5][5]= -2.0;
	xxmin[0][1]=xxmax[0][1]=xxmin[1][0]=xxmax[1][0]=  2.0;
	xxmin[0][5]=xxmax[0][5]=xxmin[1][5]=xxmax[1][5]=  2.0;
	xxmin[5][0]=xxmax[5][0]=xxmin[5][1]=xxmax[5][1]=  2.0;
 
	interMath::down(); 
	xmin[0]= 2.0*(-z[0] + x[1] + x[5]);
	xmin[1]= 2.0*(-z[1] + x[0] + x[5]);
	xmin[5]= 2.0*(-z[5] + x[0] + x[1]);
 
	interMath::up();
	xmax[5]= 2.0*(-x[5] + z[0] + z[1]);
	xmax[0]= 2.0*(-x[0] + z[1] + z[5]);
	xmax[1]= 2.0*(-x[1] + z[0] + z[5]);
 
	// compute function max; still in up mode:
	for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
		if (xmin[i]>=0.0) xa[i]=za[i];
		else if (xmax[i]<=0.0) za[i]=xa[i];
		}
	vmax = xa[0]*(-xa[0])+(-xa[1])*xa[1]+(-xa[5])*xa[5]+
		2.0*(za[0]*za[1]+za[1]*za[5]+za[5]*za[0]);
 
	interMath::down();
	for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
		if (xmin[i]>=0.0) za[i]=xa[i];
		else if (xmax[i]<=0.0) xa[i]=za[i];
		}
	vmin = za[0]*(-za[0])+(-za[1])*za[1]+(-za[5])*za[5]+
		2.0*(xa[0]*xa[1]+xa[1]*xa[5]+xa[5]*xa[0]);
 
	f = interval(vmin,vmax);
	for (i=0;i<6;i++) Df[i]=interval(xmin[i],xmax[i]);
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		DDf[i][j]=interval(xxmin[i][j],xxmax[i][j]);
	}

int secondDerive::setU126(const double x[6],const double z[6], interval DDf[6][6])
	{
	interval f,Df[6];
	::setU126(x,z,f,Df,DDf);
	return 1;
	}

void setU135(const double x[6],const double z[6],
	interval& f, interval Df[6], interval DDf[6][6])
	{
	double xx[6] = {x[0],x[2],x[1],x[3],x[5],x[4]};
	double zz[6] = {z[0],z[2],z[1],z[3],z[5],z[4]};
	interval Dg[6],DDg[6][6];
	::setU126(xx,zz,f,Dg,DDg);
	int k[6]={0,2,1,3,5,4};
	int i,j;
	for (i=0;i<6;i++) Df[i]=Dg[k[i]];
	for (i=0;i<6;i++) for (j=0;j<6;j++) DDf[i][j]=DDg[k[i]][k[j]];
	}

int secondDerive::setU135(const double x[6],const double z[6], interval DDf[6][6])
	{
	interval f,Df[6];
	::setU135(x,z,f,Df,DDf);
	return 1;
	}


// a = Sqrt[x1 x2 x3] + (x2+x3-x4)Sqrt[x1]/2 + (x1+x3-x5)Sqrt[x2]/2 +
//			(x1+x2-x6)Sqrt[x3]/2;
static int setA(const double x[6],const double z[6],
	interval& f, interval Df[6], interval DDf[6][6])
	{
	double vmin, vmax, xmin[6], xmax[6], xxmin[6][6], xxmax[6][6];
	int i,j;
 
	for (i=0;i<6;i++) for (j=0;j<6;j++)  xxmin[i][j]=xxmax[i][j]=0.0;
 
	double tx,tz,sqz,sqx;
	double hn0,hn1,hn2,hu0,hu1,hu2;
	interval y[3],xx[6];
	for (i=0;i<6;i++) 
		xx[i]=interval(x[i],z[i]); 
	for (i=0;i<3;i++) y[i]=interMath::sqrt(xx[i]);
	
	interMath::up();
	sqz= (interMath::sup(y[0]))*(interMath::sup(y[1]))*(interMath::sup(y[2]));
 
	interMath::down();
	sqx= (interMath::inf(y[0]))*(interMath::inf(y[1]))*(interMath::inf(y[2]));
	if ((sqz</*limit.h*/DBL_EPSILON)||
		(interMath::inf(y[0])<DBL_EPSILON)||
		(interMath::inf(y[1])<DBL_EPSILON)||
		(interMath::inf(y[2])<DBL_EPSILON)||
		(x[0]<DBL_EPSILON)||
		(x[1]<DBL_EPSILON)||
		(x[2]<DBL_EPSILON)||
		(z[0]<DBL_EPSILON)||
		(z[1]<DBL_EPSILON)||
		(z[2]<DBL_EPSILON)||
		(sqx<DBL_EPSILON)) return 0;
	tx = 1.0/sqz;
	hn0= 1.0/interMath::sup(y[0]); hn1=1.0/interMath::sup(y[1]); hn2=1.0/interMath::sup(y[2]);
 
	interMath::up();
	tz = 1.0/sqx; 
	hu0= 1.0/interMath::inf(y[0]); hu1=1.0/interMath::inf(y[1]); hu2=1.0/interMath::inf(y[2]);
	
	interval v,v0,v1,v2,u0,u1,u2; // 
	// on the first pass leave out the factor of four.
	v0 = (xx[1]+xx[2]-xx[3])/(y[0]);
	v1 = (xx[0]+xx[2]-xx[4])/y[1];
	v2 = (xx[0]+xx[1]-xx[5])/y[2];
	u0 = -v0/xx[0];
	u1 = -v1/xx[1];
	u2 = -v2/xx[2];
 
	interMath::down();
	xmin[0] = (interMath::inf(y[1])+interMath::inf(y[2])+x[1]*x[2]*tx+interMath::inf(v0)/2.0)/2.0;
	xmin[1] = (interMath::inf(y[0])+interMath::inf(y[2])+x[0]*x[2]*tx + interMath::inf(v1)/2.0)/2.0;
	xmin[2]= (interMath::inf(y[0])+interMath::inf(y[1])+x[0]*x[1]*tx+ interMath::inf(v2)/2.0)/2.0;
	xxmin[0][0]= ((z[1]*(-z[2]))*tz)/x[0] + interMath::inf(u0)/2.0;
	xxmin[1][1]= (((-z[0])*z[2])*tz)/x[1] + interMath::inf(u1)/2.0;
	xxmin[2][2]= (((-z[0])*z[1])*tz)/x[2] + interMath::inf(u2)/2.0;
	xxmin[0][1]= hn0 + hn1 + x[2]*tx;
	xxmin[0][2]= hn0 + hn2 + x[1]*tx;
	xxmin[0][3]= -hu0; 
	xxmin[1][2]= hn1 +hn2+ x[0]*tx;
	xxmin[1][4]= -hu1; 
	xxmin[2][5]= -hu2; 
 
	interMath::up();
	xmax[0] = (interMath::sup(y[1])+interMath::sup(y[2])+z[1]*z[2]*tz+interMath::sup(v0)/2.0)/2.0;
	xmax[1] = (interMath::sup(y[0])+interMath::sup(y[2])+z[0]*z[2]*tz + interMath::sup(v1)/2.0)/2.0;
	xmax[2]= (interMath::sup(y[0])+interMath::sup(y[1])+z[0]*z[1]*tz+ interMath::sup(v2)/2.0)/2.0;
	xxmax[0][0]= ((x[1]*(-x[2]))*tx)/z[0] +interMath::sup(u0)/2.0;
	xxmax[1][1]= ((x[0]*(-x[2]))*tx)/z[1] +interMath::sup(u1)/2.0;
	xxmax[2][2]= ((x[0]*(-x[1]))*tz)/z[2] +interMath::sup(u2)/2.0;
	xxmax[0][1]= hu0 + hu1 + z[2]*tz;
	xxmax[0][2]= hu0 + hu2 + z[1]*tz;
	xxmax[0][3]= -hn0;
	xxmax[1][2]= hu1 + hu2+ z[0]*tz;
	xxmax[1][4]= -hn1;
	xxmax[2][5]= -hn2;
 
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		{
		xxmin[i][j]=xxmin[j][i];
		xxmax[i][j]=xxmax[j][i];
		}
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		{
		xxmin[i][j] /= 4.0; xxmax[i][j] /= 4.0;
		}
 
	xmin[3]= -interMath::sup(y[0])/2.0; xmax[3]= -interMath::inf(y[0])/2.0;
	xmin[4]= -interMath::sup(y[1])/2.0; xmax[4]= -interMath::inf(y[1])/2.0;
	xmin[5]= -interMath::sup(y[2])/2.0; xmax[5]= -interMath::inf(y[2])/2.0;
 
	v = y[0]*(xx[1]+xx[2]-xx[3]) + y[1]*(xx[0]+xx[2]-xx[4])
		+ y[2]*(xx[0]+xx[1]-xx[5]);
	interMath::up();
	vmax = sqz+interMath::sup(v)/2.0;
	interMath::down();
	vmin = sqx+interMath::inf(v)/2.0;
 
	f = interval(vmin,vmax);
	for (i=0;i<6;i++) Df[i]=interval(xmin[i],xmax[i]);
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		DDf[i][j]=interval(xxmin[i][j],xxmax[i][j]);
	return 1;
	}

void setDelta(const double x[6],const double z[6],
	interval& f, interval Df[6], interval DDf[6][6])
	{
	double vmin, vmax, xmin[6], xmax[6], xxmin[6][6], xxmax[6][6];
	double xa[6],za[6];
	int i,j;
 
	interMath::down(); 
	xxmin[0][0]= -2.0*z[3]; 
	xxmin[0][1]= x[3]+x[4]-z[5]; 
	xxmin[0][2]= x[3]-z[4]+x[5]; 
	xxmin[0][3]= -2.0*z[0]+x[1]+x[2]-2.0*z[3]+x[4]+x[5];
	xxmin[0][4]= x[1]-z[2]+x[3]; 
	xxmin[0][5]= -z[1]+x[2]+x[3]; 
 
	xxmin[1][1]= -2.0*z[4]; 
	xxmin[1][2]= -z[3]+x[4]+x[5]; 
	xxmin[1][3]= x[0]-z[2]+x[4]; 
	xxmin[1][4]= x[0]-2.0*z[1]+x[2]+x[3]-2.0*z[4]+x[5];
	xxmin[1][5]= -z[0]+x[2]+x[4]; 
 
	xxmin[2][2]= -2.0*z[5]; 
	xxmin[2][3]= x[0]-z[1]+x[5]; 
	xxmin[2][4]= -z[0]+x[1]+x[5]; 
	xxmin[2][5]= x[0]+x[1]-2.0*z[2]+x[3]+x[4]-2.0*z[5];
 
	xxmin[3][3]= -2.0*z[0]; 
	xxmin[3][4]= x[0]+x[1]-z[5]; 
	xxmin[3][5]= x[0]+x[2]-z[4]; 
	xxmin[4][4]= -2.0*z[1]; 
	xxmin[4][5]= x[1]+x[2]-z[3]; 
	xxmin[5][5]= -2.0*z[2]; 
 
	interMath::up();
	xxmax[0][0] = -2.0*x[3];
	xxmax[0][1]= z[3]+z[4]-x[5];
	xxmax[0][2]= z[3]-x[4]+z[5];
	xxmax[0][3]= -2.0*x[0]+z[1]+z[2]-2.0*x[3]+z[4]+z[5];
	xxmax[0][4]= z[1]-x[2]+z[3];
	xxmax[0][5]= -x[1]+z[2]+z[3];
 
	xxmax[1][1]= -2.0*x[4];
	xxmax[1][2]= -x[3]+z[4]+z[5];
	xxmax[1][3]= z[0]-x[2]+z[4];
	xxmax[1][4]= z[0]-2.0*x[1]+z[2]+z[3]-2.0*x[4]+z[5];
	xxmax[1][5]= -x[0]+z[2]+z[4];
 
	xxmax[2][2]= -2.0*x[5];
	xxmax[2][3]=z[0]-x[1]+z[5];
	xxmax[2][4]= -x[0]+z[1]+z[5];
	xxmax[2][5]= z[0]+z[1]-2.0*x[2]+z[3]+z[4]-2.0*x[5];
 
	xxmax[3][3]= -2.0*x[0];
	xxmax[3][4]= z[0]+z[1]-x[5];
	xxmax[3][5]= z[0]+z[2]-x[4];
	xxmax[4][4]= -2.0*x[1];
	xxmax[4][5]= z[1]+z[2]-x[3];
	xxmax[5][5]= -2.0*x[2];
 
	for (i=0;i<6;i++) for (j=0;j<i;j++) 
		{ xxmin[i][j]=xxmin[j][i]; xxmax[i][j]=xxmax[j][i]; }
 
	interMath::up(); 
	// now for xmax[j]
	for (j=0;j<6;j++)
	{
	for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
		if (xxmin[j][i]>=0.0) xa[i]=za[i];
		else if (xxmax[j][i]<=0.0) za[i]=xa[i];
		}
		switch (j) {
		  case 0: xmax[j]= 2.0*(-xa[0])*xa[3]+za[1]*za[3]+za[2]*za[3]
				+(-xa[3])*xa[3]+za[1]*za[4]+(-xa[2])*xa[4]
				+za[3]*za[4]+(-x[1])*x[5]+za[2]*za[5]
				+za[3]*za[5];
				break;
		  case 1: xmax[j]= za[4]*(za[0]+za[2]+za[3]+za[5])
				   +(-xa[4])*xa[1]+(-xa[4])*xa[4]
				   +(-xa[2])*xa[3]+(-xa[1])*xa[4]+(-xa[0])*xa[5]
				   +za[0]*za[3]+za[2]*za[5];
				break;
		  case 2: xmax[j]= za[5]*(za[0]+za[1]+za[3]+za[4])
					+za[0]*za[3]+za[1]*za[4]
				+(-xa[5])*xa[2]+(-xa[5])*xa[5]
				+(-xa[1])*xa[3]+(-xa[0])*xa[4]+(-xa[2])*xa[5];
				break;
		  case 3: xmax[j]= za[0]*(za[1]+za[2]+za[4]+za[5])
				+ za[1]*za[4]+za[2]*za[5]
				+(-xa[0])*xa[0]+(-xa[0])*xa[3]
				+(-xa[1])*xa[2]+(-xa[0])*xa[3]+(-xa[4])*xa[5];
				break;
		  case 4: xmax[j]= za[1]*(za[0]+za[2]+za[3]+za[5])
				+ za[0]*za[3]+za[2]*za[5]
				+(-xa[1])*xa[1]+(-xa[1])*xa[4]
				+(-xa[0])*xa[2]+(-xa[1])*xa[4]+(-xa[3])*xa[5];
				break;
		  case 5: xmax[j]= za[2]*(za[0]+za[1]+za[3]+za[4])
				+ za[0]*za[3]+za[1]*za[4]
				+(-xa[2])*xa[2]+(-xa[2])*xa[5]
				+(-xa[0])*xa[1]+(-xa[3])*xa[4]+(-xa[2])*xa[5];
				break;
		}
	}
 
	interMath::down(); 
	// now for xmin[j]
	for (j=0;j<6;j++)
	{
	for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
		if (xxmin[j][i]>=0.0) za[i]=xa[i];
		else if (xxmax[j][i]<=0.0) xa[i]=za[i];
		}
		switch (j) {
		  case 0: xmin[j]= 2.0*(-za[0])*za[3]+xa[1]*xa[3]+xa[2]*xa[3]
				+(-za[3])*za[3]+xa[1]*xa[4]+(-za[2])*za[4]
				+xa[3]*xa[4]+(-z[1])*z[5]+xa[2]*xa[5]
				+xa[3]*xa[5];
				break;
		  case 1: xmin[j]= xa[4]*(xa[0]+xa[2]+xa[3]+xa[5])
				   +(-za[4])*za[1]+(-za[4])*za[4]
				   +(-za[2])*za[3]+(-za[1])*za[4]+(-za[0])*za[5]
				   +xa[0]*xa[3]+xa[2]*xa[5];
				break;
		  case 2: xmin[j]= xa[5]*(xa[0]+xa[1]+xa[3]+xa[4])
					+xa[0]*xa[3]+xa[1]*xa[4]
				+(-za[5])*za[2]+(-za[5])*za[5]
				+(-za[1])*za[3]+(-za[0])*za[4]+(-za[2])*za[5];
				break;
		  case 3: xmin[j]= xa[0]*(xa[1]+xa[2]+xa[4]+xa[5])
				+ xa[1]*xa[4]+xa[2]*xa[5]
				+(-za[0])*za[0]+(-za[0])*za[3]
				+(-za[1])*za[2]+(-za[0])*za[3]+(-za[4])*za[5];
				break;
		  case 4: xmin[j]= xa[1]*(xa[0]+xa[2]+xa[3]+xa[5])
				+ xa[0]*xa[3]+xa[2]*xa[5]
				+(-za[1])*za[1]+(-za[1])*za[4]
				+(-za[0])*za[2]+(-za[1])*za[4]+(-za[3])*za[5];
				break;
		  case 5: xmin[j]= xa[2]*(xa[0]+xa[1]+xa[3]+xa[4])
				+ xa[0]*xa[3]+xa[1]*xa[4]
				+(-za[2])*za[2]+(-za[2])*za[5]
				+(-za[0])*za[1]+(-za[3])*za[4]+(-za[2])*za[5];
				break;
		}
	}
 
	interMath::up();	
	// now for vmax
	for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
		if (xmin[i]>=0.0) xa[i]=za[i];
		else if (xmax[i]<=0.0) za[i]=xa[i];
		}
	vmax = (xa[1]*(-xa[2]))*xa[3]+ ((-xa[0])*xa[2])*xa[4]
			+((-xa[0])*xa[1])*xa[5]
			+((-xa[3])*xa[4])*xa[5]
		+za[2]*za[5]*(za[0]+za[1]+za[3]+za[4])
		+((-xa[2])*xa[5])*xa[2]+((-xa[2])*xa[5])*xa[5]
		+za[1]*za[4]*(za[0]+za[2]+za[3]+za[5])
		+((-xa[1])*xa[4])*xa[1]+((-xa[1])*xa[4])*xa[4]
		+za[0]*za[3]*(za[1]+za[2]+za[4]+za[5])
		+((-xa[0])*xa[3])*xa[0]+((-xa[0])*xa[3])*xa[3];
	
	for (i=0;i<6;i++) { xa[i]=x[i]; za[i]=z[i]; 
		if (xmin[i]>=0.0) za[i]=xa[i];
		else if (xmax[i]<=0.0) xa[i]=za[i];
		}
 
	interMath::down(); 
	vmin = (za[1]*(-za[2]))*za[3]+((-za[0])*za[2])*za[4]
		+((-za[0])*za[1])*za[5]
			+((-za[3])*za[4])*za[5]
		+xa[2]*xa[5]*(xa[0]+xa[1]+xa[3]+xa[4])
		+((-za[2])*za[5])*za[2]+((-za[2])*za[5])*za[5]
		+xa[1]*xa[4]*(xa[0]+xa[2]+xa[3]+xa[5])
		+((-za[1])*za[4])*za[1]+((-za[1])*za[4])*za[4]
		+xa[0]*xa[3]*(xa[1]+xa[2]+xa[4]+xa[5])
		+((-za[0])*za[3])*za[0]+((-za[0])*za[3])*za[3];
	f = interval(vmin,vmax);
	for (i=0;i<6;i++) Df[i]=interval(xmin[i],xmax[i]);
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		DDf[i][j]=interval(xxmin[i][j],xxmax[i][j]);
	} // end of setDelta;

int secondDerive::setDelta(const double x[6],const double z[6],interval DDf[6][6])
	{
	interval f,Df[6];
	::setDelta(x,z,f,Df,DDf);
	return 1;
	}

int secondDerive::setChi2over4uDelta(const double x[6],const double z[6],double DDf[6][6])
	{ // this + eta^2 126 is the circumradius squared of a simplex.
	int i,j;
	interval d,Dd[6],DDd[6][6];
	interval c,Dc[6],DDc[6][6];
	interval u,Du[6],DDu[6][6];
	::setDelta(x,z,d,Dd,DDd);
	::setChi126(x,z,c,Dc,DDc);
	::setU126(x,z,u,Du,DDu);
	if (interMath::inf(u)<=1.0e-5) return 0;
	if (interMath::inf(d)<=1.0e-5) return 0;
	interval c2,Dc2[6],DDc2[6][6];
	Leibniz::product(c,Dc,DDc,c,Dc,DDc,c2,Dc2,DDc2);
	interval den,Dden[6],DDden[6][6];
	Leibniz::product(u,Du,DDu,d,Dd,DDd,den,Dden,DDden);
	interval q,Dq[6],DDq[6][6];
	if (!Leibniz::quotient(c2,Dc2,DDc2,den,Dden,DDden,q,Dq,DDq)) return 0;
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		DDf[i][j]= interMath::sup(interMath::max(DDq[i][j],-DDq[i][j]))/4.0;
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDf[i][j]= DDf[j][i];
	return 1;
	}

	//////////
	//
	// numerator in dihedral function. Take the derivative wrt opposite edge.
	// deltaX=  -(x1*x2) - x0*x3 + x1*x4 + x2*x5 - x4*x5 + 
    // 						x0*(-x0 + x1 + x2 - x3 + x4 + x5);
	// deltaX = D[Delta @@ Sqrt[{x0,x1,x2,x3,x4,x5}],x3], where Delta
	// is the Mathematica function giving Delta in terms of y-variables.
	//
static void setDeltaX(const double x[6],const double z[6],
	interval& f, interval Df[6], interval DDf[6][6])
	{
	static const interval zero("0");
	static const interval one("1");
	static const interval two("2");
	double vmin, vmax ;
	double xa[6],za[6];
	interval xx[6];
	int i,j;
 
	for (i=0;i<6;i++) for (j=0;j<6;j++) DDf[i][j]=zero;
	for (i=0;i<6;i++) xx[i] = interval(x[i],z[i]);
	DDf[0][0] = DDf[0][3] = -two;
	DDf[0][1]=DDf[0][2]=DDf[0][4]=DDf[0][5]=one;
	DDf[1][2]=-one; DDf[1][4]=one;
	DDf[2][5]= one;
	DDf[4][5]=-one;
	for (i=0;i<6;i++) for (j=0;j<i;j++) DDf[i][j]=DDf[j][i];
	Df[0]= -two*xx[0]+xx[1]+xx[2]-two*xx[3]+xx[4]+xx[5];
	Df[1]= xx[0]-xx[2]+xx[4];
	Df[2]= xx[0]-xx[1]+xx[5];
	Df[3]= -two*xx[0];
	Df[4]= xx[0]+xx[1]-xx[5];
	Df[5]= xx[0]+xx[2]-xx[4];
 
	interMath::up();
	// now for vmax;
	for (i=0;i<6;i++) 
		{ xa[i]=x[i]; za[i]=z[i]; 
		if (interMath::inf(Df[i])>=0.0) xa[i]=za[i];
		else if (interMath::sup(Df[i])<=0.0) za[i]=xa[i];
		}
	vmax = xa[1]*(-xa[2])+(-xa[0])*xa[3] +za[1]*za[4]+za[2]*za[5]
		+(-xa[4])*xa[5]
		+za[0]*(za[1]+za[2]+za[4]+za[5])
		+(-xa[0])*xa[0]+(-xa[0])*xa[3];
 
	interMath::down();
	for (i=0;i<6;i++) 
		{ xa[i]=x[i]; za[i]=z[i]; 
		if (interMath::inf(Df[i])>=0.0) za[i]=xa[i];
		else if (interMath::sup(Df[i])<=0.0) xa[i]=za[i];
		}
	vmin = za[1]*(-za[2])+ 
		(-za[0])*za[3]+xa[1]*xa[4]+xa[2]*xa[5]+(-za[4])*za[5]  +
		xa[0]*(xa[1]+xa[2]+xa[4]+xa[5])
		+(-za[0])*za[0]+(-za[0])*za[3];
	f = interval(vmin,vmax);
	}
	

// now start building up more complex functions with the product rule, etc.


void Leibniz::product(const interval& u,const interval Du[6],const interval DDu[6][6],
	const interval& v,const interval Dv[6],const interval DDv[6][6],
	interval& uv,interval Duv[6],interval DDuv[6][6])
	{
	int i,j;
	uv = u*v;
	for (i=0;i<6;i++) Duv[i] = u*Dv[i] + v*Du[i];
	interval DuDv[6][6];
	for (i=0;i<6;i++) for (j=0;j<6;j++) DuDv[i][j]=Du[i]*Dv[j];
	interval uDDv[6][6],vDDu[6][6];
	half_array_multiply(v,DDu,vDDu);
	half_array_multiply(u,DDv,uDDv);
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		DDuv[i][j]= uDDv[i][j]+DuDv[i][j]+DuDv[j][i]+vDDu[i][j];
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDuv[i][j]= DDuv[j][i];
	}

int Dsqrt(const interval&u,const interval Du[6],const interval DDu[6][6],
	interval& sqrt_u,interval Dsqrt_u[6],interval DDsqrt_u[6][6])
	{
	int i,j;
	if (interMath::inf(u)<=DBL_EPSILON) return 0;
	sqrt_u = interMath::sqrt(u);
	if (interMath::inf(sqrt_u)<DBL_EPSILON) return 0;
	interval t = interval(   
		(interMath::down(), 0.5/interMath::sup(sqrt_u)),
		(interMath::up(), 0.5/interMath::inf(sqrt_u)));
 
	for (i=0;i<6;i++) Dsqrt_u[i]= Du[i]*t;
 
	interval v = interval((interMath::down(), (-0.5)/interMath::inf(u)),(interMath::up(), (-0.5)/interMath::sup(u)));
 
	interval vDu[6];
	for (i=0;i<6;i++) vDu[i] = Du[i]*v;
 
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		DDsqrt_u[i][j] =(Du[i]*vDu[j] + DDu[i][j])*t;
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDsqrt_u[i][j] = DDsqrt_u[j][i];
	return 1;
	}

int Leibniz::quotient(const interval& a,const interval Da[6],const interval DDa[6][6],	
	const interval& b,const interval Db[6],const interval DDb[6][6],
	interval& v,interval Dv[6],interval DDv[6][6])
	{
	static const interval one("1");
	static const interval two("2");
	int i,j;
	double smallDen = 1.0e-08;
	if ((interMath::inf(b)< smallDen)&&(interMath::sup(b)> -smallDen)) return 0;
	v = a/b;
	interval b2 = one/(b*b);
	interval t = -two*b2/b;
	interval r[6];
	for (i=0;i<6;i++) r[i] = (Da[i]*b- a*Db[i]);
	for (i=0;i<6;i++) Dv[i] = r[i]*b2;
	for (i=0;i<6;i++) r[i] = r[i]*t;
	interval DaDb[6][6];
	for (i=0;i<6;i++) for (j=0;j<6;j++) DaDb[i][j]=Da[i]*Db[j];
 
	interval bDDa[6][6]; half_array_multiply(b,DDa,bDDa);
	interval aDDb[6][6]; half_array_multiply(a,DDb,aDDb);
 
	interval DDu[6][6];
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		DDu[i][j]= (bDDa[i][j]+DaDb[i][j]-DaDb[j][i]-aDDb[i][j]);
	half_array_multiply(b2,DDu,DDv);
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		DDv[i][j] = DDv[i][j] + r[i]*Db[j];
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDv[i][j]= DDv[j][i];
	return 1;
	}

int secondDerive::setDihedral(const double x[6],const double z[6],
	const interval& s,const interval Ds[6],
	const interval DDs[6][6],
	interval& h,interval Dh[6],interval DDh[6][6])
	{
	static const interval one("1");
	static const interval two("2");
	static const interval pi2 = "1.57079632679489661923132169164";
	int i,j;
	interval ty1 = interMath::sqrt(interval(4.0*x[0],4.0*z[0]));
	interval u126,Du126[6],DDu126[6][6];
	::setU126(x,z,u126,Du126,DDu126);
	
	interval u135,Du135[6],DDu135[6][6];
	::setU135(x,z,u135,Du135,DDu135);
	
	interval dX,DdX[6],DDdX[6][6];
	::setDeltaX(x,z,dX,DdX,DDdX);
 
	interval b,Db[6],DDb[6][6];
	b = s*ty1;
	if ((interMath::inf(s)<=0.0)) return 0;
	if ((interMath::inf(b)<=0.0)&&(interMath::sup(b)>=0.0)) return 0;
	if ((interMath::inf(u135)<=0.0)&&(interMath::sup(u135)>=0.0)) return 0;
	if ((interMath::inf(u126)<=0.0)&&(interMath::sup(u126)>=0.0)) return 0;
	h = pi2+ interMath::atan(-dX/b);
	for (i=0;i<6;i++) Db[i]= Ds[i]*ty1;
	interval ry1 = two/ty1;
	Db[0] = Db[0]+ s*ry1;
	interval c[6];
	for (i=0;i<6;i++) c[i]= -DdX[i]*b + dX*Db[i];
 
	interval ru = one/(u135*u126);
 
	for (i=0;i<6;i++) Dh[i]= c[i]*ru;
	Dh[3]= ty1/(two*s);
	
	interval ru126 = one/u126;
	interval ru135 = one/u135;
 
	for (i=0;i<6;i++) for (j=i;j<6;j++) DDb[i][j]= DDs[i][j]*ty1;
	for (i=1;i<6;i++) DDb[0][i] = DDb[0][i] + Ds[i]*ry1;
	DDb[0][0] = DDb[0][0] + two*Ds[0]*ry1 
			- s*ry1/interval(2.0*x[0],2.0*z[0]);
	interval U[6];
	for (i=0;i<6;i++)
		U[i]= Du135[i]*ru135+Du126[i]*ru126;
	interval bDDdX[6][6];
	half_array_multiply(b,DDdX,bDDdX);
	interval XDDb[6][6];
	half_array_multiply(dX,DDb,XDDb);
 
	for (i=0;i<6;i++) for (j=i+1;j<6;j++)
		DDh[i][j]= ru*(-bDDdX[i][j] - DdX[i]*Db[j] +
				DdX[j]*Db[i] + XDDb[i][j]) - Dh[i]*U[j];
	for (i=0;i<6;i++) 
		DDh[i][i]= ru*(-bDDdX[i][i]+ XDDb[i][i]) - Dh[i]*U[i];
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDh[i][j]= DDh[j][i];
	return 1;
	}

	
int secondDerive::setDih2(const double x[6],const double z[6],
	const interval &s,const interval Ds[6], 
	const interval DDs[6][6],
	interval&h, interval Dh[6],interval DDh[6][6])
	{
        double xx[6],zz[6];
	interval Dt[6],DDt[6][6],Dsn[6],DDsn[6][6];
	int i,j;
        // k is the reassignment.
        static int k[6] = {1,0,2,4,3,5};
        for (i=0;i<6;i++) { xx[i]=x[k[i]]; zz[i]=z[k[i]];  
			    Dsn[i]=Ds[k[i]];}
	for (i=0;i<6;i++) for (j=0;j<6;j++)
			DDsn[i][j]=DDs[k[i]][k[j]];
        if (!(setDihedral(xx,zz,s,Dsn,DDsn,h,Dt,DDt))) return 0;
	for (i=0;i<6;i++) Dh[i]=Dt[k[i]];
        for (i=0;i<6;i++) for (j=0;j<6;j++)
                DDh[i][j] = DDt[k[i]][k[j]];
	return 1;
        }

int secondDerive::setDih3(const double x[6],const double z[6],
	const interval &s,const interval Ds[6], 
	const interval DDs[6][6],
	interval&h, interval Dh[6],interval DDh[6][6])
	{
        double xx[6],zz[6];
	interval Dt[6],DDt[6][6],Dsn[6],DDsn[6][6];
	int i,j;
        // k is the reassignment.
        static int k[6] = {2,1,0,5,4,3};
        for (i=0;i<6;i++) { xx[i]=x[k[i]]; zz[i]=z[k[i]];  
			    Dsn[i]=Ds[k[i]];}
	for (i=0;i<6;i++) for (j=0;j<6;j++)
			DDsn[i][j]=DDs[k[i]][k[j]];
        if (!(setDihedral(xx,zz,s,Dsn,DDsn,h,Dt,DDt))) return 0;
	for (i=0;i<6;i++) Dh[i]=Dt[k[i]];
        for (i=0;i<6;i++) for (j=0;j<6;j++)
                DDh[i][j] = DDt[k[i]][k[j]];
	return 1;
        }

static int Adihfactor(double x,double z,interval t,interval& r,interval& Dr,
		interval& DDr)
	{
	// (1-h/t)*(pretilde(t,t)-pretilde(h,t));  h = sqrt(x)/2;
	// (1-h/t)*(phi(h,t)-phi(t,t));
	// A(h), in the notation of SP.III.A.4. (also appearing other places).
	// Adih = Adihfactor*dih
	static const interval zero("0");
	static const interval two("2");
	static const interval three("3");
	static const interval four("4");
	interval twicet = two*t;
	double qu,qn;
	interval t2=t*t;
	interMath::up(); qu = sqrt(z); interMath::down(); qn = sqrt(x);
	interval q = interval(qn,qu);
	interval xx = interval(x,z);
	interval xxq = xx*q;
	if (qn >= interMath::sup(twicet)) 
		{ r=Dr=DDr=zero; return 1; }
	if ((interMath::inf(xxq)<=0.0)&& (interMath::sup(xxq)>=0.0)) return 0;
	static const interval dt = "0.7209029495174650928412448"; // doct
	static const interval dt12 = "0.06007524579312209107010373625"; //doct/12;
	interval dtt2 = dt*t2;
	static const interval N16("16");
	static const interval N8("8");
	DDr = dtt2/(four*xxq) + dt/(N16*q);
	Dr =  -dtt2/(two*q) + dt*q/N8;
	r = (four*dtt2*t)/three - dtt2*q + dt12*xxq;
	if (qu>interMath::inf(twicet)) 
		{ 
		r = interMath::combine(r,zero); 
		Dr=interMath::combine(Dr,zero);
		DDr=interMath::combine(DDr,zero); 
		}
	return 1;
	}

	////////
	//
	// Adih = A[y1/2] dih(S).
	// Adih = Adihfactor*dih.
	//
int Adih(double x,double z,interval trunc,
	const interval& d,const interval Dd[6],const interval DDd[6][6],
	interval DDc[6][6])
	{
	interval r,Dr,DDr;
	if (!(Adihfactor(x,z,trunc,r,Dr,DDr))) return 0;
	int i,j;
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		DDc[i][j] = r*DDd[i][j];
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDc[i][j] = DDc[j][i];
	for (i=0;i<6;i++) DDc[0][i] = DDc[0][i] + Dr*Dd[i];
	for (i=0;i<6;i++) DDc[i][0] = DDc[i][0] + Dr*Dd[i];
	DDc[0][0] = DDc[0][0] + DDr*d;
	return 1;
	}

	////////
	//
	// Adih2 = A[y2/2] dih2(S)
	//
int Adih2(double x,double z,interval trunc,
	const interval& d,const interval Dd[6],const interval DDd[6][6],
	interval DDc[6][6])
	// [x,z] is the second edge,
	// d,Dd,DDd are the output from setDih2 = dihedral2 & its derivatives
	// DDc output
	{
	interval r,Dr,DDr;
	if (!Adihfactor(x,z,trunc,r,Dr,DDr)) return 0;
	int i,j;
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		DDc[i][j] = r*DDd[i][j];
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDc[i][j] = DDc[j][i];
	for (i=0;i<6;i++) DDc[1][i] = DDc[1][i] + Dr*Dd[i];
	for (i=0;i<6;i++) DDc[i][1] = DDc[i][1] + Dr*Dd[i];
	DDc[1][1] = DDc[1][1] + DDr*d;
	return 1;
	}

	////////
	//
	// Adih3 = A[y3/2] dih3(S)
	//
int Adih3(double x,double z,interval trunc,
	const interval& d,const interval Dd[6],const interval DDd[6][6],
	interval DDc[6][6])
	// [x,z] is the third edge,
	// d,Dd,DDd are the output from setDih3 = dihedral3 & its derivatives
	// DDc output
	{
	interval r,Dr,DDr;
	if (!Adihfactor(x,z,trunc,r,Dr,DDr)) return 0;
	int i,j;
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		DDc[i][j] = r*DDd[i][j];
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDc[i][j] = DDc[j][i];
	for (i=0;i<6;i++) DDc[2][i] = DDc[2][i] + Dr*Dd[i];
	for (i=0;i<6;i++) DDc[i][2] = DDc[i][2] + Dr*Dd[i];
	DDc[2][2] = DDc[2][2] + DDr*d;
	return 1;
	}

int secondDerive::setVorSqc
	(const double x[6],const double z[6],double DDv[6][6]) 
	{
	int i,j;
	static const interval one("1");
	static const interval two("2");
	static const interval three("3");
	static const interval four("4");
	static const interval t("1.41421356237309504880168872421");
	static const interval doct("0.72090294951746509284124483502");
	static const interval tildeV = 
	 four*(one-doct*t*t*t)/three;
	static const interval doct4=four*doct;
	static const interval tdoct4quoin= 
		two*interval::wideInterval("-0.13","0.13")*doct4; 
		 // nondiag max abs = 0.10629. 
		 // from out.quoin.simplex.sqrt.
		 // factor of 2 because 2 quoins on
		 //   each face
	static const interval s63("6.3001");
	if ((z[0]>interMath::sup(s63))||
		(z[1]>interMath::sup(s63))||
		(z[2]>interMath::sup(s63)))
			return 0; // because out.quoin.simplex.sqrt is used.
	interval s,Ds[6],DDs[6][6];
	interval DDf1[6][6],DDf2[6][6],DDf3[6][6],DDx[6][6];
	interval f,Df[6];
	interval DDx1[6][6],DDx2[6][6],DDx3[6][6];
	if (!setSqrtDelta(x,z,s,Ds,DDs)) return 0;
	if (!setDihedral(x,z,s,Ds,DDs,f,Df,DDf1)) return 0;
	if (!Adih(x[0],z[0],t, f,Df,DDf1,DDx1)) return 0;
	if (!setDih2(x,z,s,Ds,DDs,f,Df,DDf2)) return 0;
	if (!Adih2(x[1],z[1],t, f,Df,DDf2,DDx2)) return 0;
	if (!setDih3(x,z,s,Ds,DDs,f,Df,DDf3)) return 0;
	if (!Adih3(x[2],z[2],t, f,Df,DDf3,DDx3)) return 0;
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		{
		DDx[i][j]=DDx1[i][j]+DDx2[i][j]+DDx3[i][j]+
			(DDf1[i][j]+DDf2[i][j]+DDf3[i][j])*tildeV;
		}
	static const interval diag = 
		two*interval::wideInterval("-0.192","0.192")*doct4;
				// diag max abs = 0.147748...
				// from out.quoin.simplex.sqrt;
	if (x[5]<=8.0)
		{
		DDx[0][1] = DDx[0][1]+tdoct4quoin;
		DDx[1][5] = DDx[1][5]+tdoct4quoin;
		DDx[0][5] = DDx[0][5]+tdoct4quoin;
		DDx[0][0] = DDx[0][0]+diag;
		DDx[1][1] = DDx[1][1]+diag;
		DDx[5][5] = DDx[5][5]+diag;
		}
	if (x[4]<=8.0)
		{
		DDx[0][2] = DDx[0][2]+tdoct4quoin;
		DDx[0][4] = DDx[0][4]+tdoct4quoin;
		DDx[2][4] = DDx[2][4]+tdoct4quoin;
		DDx[0][0] = DDx[0][0]+diag;
		DDx[2][2] = DDx[2][2]+diag;
		DDx[4][4] = DDx[4][4]+diag;
		}
	if (x[3]<=8.0)
		{
		DDx[1][2] = DDx[1][2]+tdoct4quoin;
		DDx[1][3] = DDx[1][3]+tdoct4quoin;
		DDx[2][3] = DDx[2][3]+tdoct4quoin;
		DDx[1][1] = DDx[1][1]+diag;
		DDx[4][4] = DDx[4][4]+diag;
		DDx[3][3] = DDx[3][3]+diag;
		}
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDx[i][j]=DDx[j][i];
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		DDv[i][j]=interMath::sup(interMath::max(DDx[i][j],-DDx[i][j]));
	return 1;
	}

static int setVorVcNoQuoin
	(const double x[6],const double z[6],interval DDx[6][6]) 
	{
	int i,j;
	static const interval one("1");
	static const interval three("3");
	static const interval four("4");
	static const interval t("1.255");
	static const interval doct("0.72090294951746509284124483502");
	static const interval tildeV = 
	 four*(one-doct*t*t*t)/three;
	static const interval doct4=four*doct;
	static const interval s63("6.3001");
	if ((z[1]>interMath::sup(s63))||(z[2]>interMath::sup(s63)))
		{ error::message("setVorVc used out of range"); 
			return 0; }
	interval s,Ds[6],DDs[6][6];
	interval DDf1[6][6],DDf2[6][6],DDf3[6][6];
	interval f,Df[6];
	interval DDx1[6][6],DDx2[6][6],DDx3[6][6];
	if (!secondDerive::setSqrtDelta(x,z,s,Ds,DDs)) return 0;
	if (!secondDerive::setDihedral(x,z,s,Ds,DDs,f,Df,DDf1)) return 0;
	if (!Adih(x[0],z[0],t, f,Df,DDf1,DDx1)) return 0;
	if (!secondDerive::setDih2(x,z,s,Ds,DDs,f,Df,DDf2)) return 0;
	if (!Adih2(x[1],z[1],t, f,Df,DDf2,DDx2)) return 0;
	if (!secondDerive::setDih3(x,z,s,Ds,DDs,f,Df,DDf3)) return 0;
	if (!Adih3(x[2],z[2],t, f,Df,DDf3,DDx3)) return 0;
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		{
		DDx[i][j]=DDx1[i][j] +DDx2[i][j]+DDx3[i][j]+
			(DDf1[i][j]+DDf2[i][j]+DDf3[i][j])*tildeV;
		}
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDx[i][j]=DDx[j][i];
	return 1;
	}

static int setVor1385NoQuoin // modified from setVorVcNoQuoin
	(const double x[6],const double z[6],interval DDx[6][6]) 
	{
	int i,j;
	static const interval one("1");
	static const interval three("3");
	static const interval four("4");
	static const interval t("1.385"); // this is the only line modif.
	static const interval doct("0.72090294951746509284124483502");
	static const interval tildeV = 
	 four*(one-doct*t*t*t)/three;
	static const interval doct4=four*doct;
	static const interval s63("6.3001");
	if ((z[1]>interMath::sup(s63))||(z[2]>interMath::sup(s63)))
		{ error::message("setVorVc used out of range"); 
			return 0; }
	interval s,Ds[6],DDs[6][6];
	interval DDf1[6][6],DDf2[6][6],DDf3[6][6];
	interval f,Df[6];
	interval DDx1[6][6],DDx2[6][6],DDx3[6][6];
	if (!secondDerive::setSqrtDelta(x,z,s,Ds,DDs)) return 0;
	if (!secondDerive::setDihedral(x,z,s,Ds,DDs,f,Df,DDf1)) return 0;
	if (!Adih(x[0],z[0],t, f,Df,DDf1,DDx1)) return 0;
	if (!secondDerive::setDih2(x,z,s,Ds,DDs,f,Df,DDf2)) return 0;
	if (!Adih2(x[1],z[1],t, f,Df,DDf2,DDx2)) return 0;
	if (!secondDerive::setDih3(x,z,s,Ds,DDs,f,Df,DDf3)) return 0;
	if (!Adih3(x[2],z[2],t, f,Df,DDf3,DDx3)) return 0;
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		{
		DDx[i][j]=DDx1[i][j] +DDx2[i][j]+DDx3[i][j]+
			(DDf1[i][j]+DDf2[i][j]+DDf3[i][j])*tildeV;
		}
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDx[i][j]=DDx[j][i];
	return 1;
	}

int secondDerive::setVorVc(const double x[6],const double z[6],double DDv[6][6]) 
	{
	interval DDx[6][6];
	static const interval two("2");
	static const interval four("4");
	static const interval doct("0.72090294951746509284124483502");
	static const interval doct4=four*doct;
	if (!setVorVcNoQuoin(x,z,DDx)) return 0;
	static const interval tdoct4quoin1255= 
		 two*interval::wideInterval("-0.004","0.004")*doct4; 
		 // nondiag max abs = 0.00364.. 
		 // from secout.quoin.simplex.1255.
	static const interval twice = two*tdoct4quoin1255;
	// i,j determine the face, hence a pair of quoins
	DDx[0][1] = DDx[0][1]+twice;
	DDx[0][2] = DDx[0][2]+twice;
	DDx[0][4] = DDx[0][4]+twice;
	DDx[0][5] = DDx[0][5]+twice;
	DDx[1][2] = DDx[1][2]+twice;
	DDx[1][3] = DDx[1][3]+twice;
	DDx[1][5] = DDx[1][5]+twice;
	DDx[2][3] = DDx[2][3]+twice;
	DDx[2][4] = DDx[2][4]+twice;
	static const interval diag = two*
		interval::wideInterval("-0.008","0.008")*doct4;
		// diag max abs = 0.00621..
		// from secout.quoin.simplex.1255;
	DDx[0][0] = DDx[0][0]+two*diag;
	DDx[1][1] = DDx[1][1]+two*diag;
	DDx[2][2] = DDx[2][2]+two*diag;
	DDx[3][3] = DDx[3][3]+diag;
	DDx[4][4] = DDx[4][4]+diag;
	DDx[5][5] = DDx[5][5]+diag;
	int i,j;
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDx[i][j]=DDx[j][i];
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		DDv[i][j]=interMath::sup( interMath::max(DDx[i][j],-DDx[i][j]));
	return 1;
	}

int secondDerive::setVor1385(const double x[6],const double z[6],double DDv[6][6]) 
	{
	interval DDx[6][6];
	static const interval two("2");
	static const interval four("4");
	static const interval doct("0.72090294951746509284124483502");
	static const interval doct4=four*doct;
	if (!setVor1385NoQuoin(x,z,DDx)) return 0;
	static const interval tdoct4quoin1385= 
		 two*interval::wideInterval("-0.06","0.06")*doct4; 
		 // nondiag max abs = 0.0538.. 
		 // from secout.quoin.simplex.1385.
	static const interval twice = two*tdoct4quoin1385;
	// i,j determine the face, hence a pair of quoins
	DDx[0][1] = DDx[0][1]+twice;
	DDx[0][2] = DDx[0][2]+twice;
	DDx[0][4] = DDx[0][4]+twice;
	DDx[0][5] = DDx[0][5]+twice;
	DDx[1][2] = DDx[1][2]+twice;
	DDx[1][3] = DDx[1][3]+twice;
	DDx[1][5] = DDx[1][5]+twice;
	DDx[2][3] = DDx[2][3]+twice;
	DDx[2][4] = DDx[2][4]+twice;
	static const interval diag = two*
		interval::wideInterval("-0.1","0.1")*doct4;
		// diag max abs = 0.0801..
		// from out.quoin.simplex.1385;
	DDx[0][0] = DDx[0][0]+two*diag;
	DDx[1][1] = DDx[1][1]+two*diag;
	DDx[2][2] = DDx[2][2]+two*diag;
	DDx[3][3] = DDx[3][3]+diag;
	DDx[4][4] = DDx[4][4]+diag;
	DDx[5][5] = DDx[5][5]+diag;
	int i,j;
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDx[i][j]=DDx[j][i];
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		DDv[i][j]=interMath::sup( interMath::max(DDx[i][j],-DDx[i][j]));
	return 1;
	}

// Not tested.
int secondDerive::setVorVcInverted( const double x[6],const double z[6],double DD[6][6])
	{
	double xx[6],zz[6],DDxz[6][6];
	int i,j;
	const int k[6]={0,5,4,3,2,1};
	for ( i=0;i<6;i++) { xx[i]=x[k[i]]; zz[i]=z[k[i]]; }
	if (!setVorVc( xx,zz,DDxz)) return 0;
	for ( i=0;i<6;i++) for ( j=0;j<6;j++) DD[k[i]][k[j]]=DDxz[i][j]; 
	return 1;
	}

int secondDerive::setSolid( const double x[6],const double z[6],
	const interval ss,const interval Ds[6],const interval DDs[6][6],
	interval DDx[6][6])
	{
	int i,j;
 
	static const interval two("2");
	interval a,Da[6],DDa[6][6];
	if (!setA( x,z,a,Da,DDa)) return 0;
	a = two*a;
	if (interMath::inf(a)<=0.0) return 0;
	for (i=0;i<6;i++) Da[i]=two*Da[i];
	for (i=0;i<6;i++) for (j=0;j<6;j++) 
		{
		DDa[i][j].hi *= 2.0;  DDa[i][j].lo *= 2.0;
		}
	
	
	// solid = 2 arctan(s/a);
	interval t = two/(a*a+ss*ss);
	interval t2= t*t;
 
	interval Dssa[6];
	for (i=0;i<6;i++) Dssa[i] = ss*Da[i]-Ds[i]*a;
	interval Daas[6];
	for (i=0;i<6;i++) Daas[i] = (ss*Ds[i]+a*Da[i])*t2;
	interval at = a*t;
	interval sst = ss*t;
	interval tDa[6]; for (i=0;i<6;i++) tDa[i]= t*Da[i];
	
	interval tDaDs[6][6];
 
	for (i=0;i<6;i++) for (j=0;j<6;j++) tDaDs[i][j]=tDa[i]*Ds[j];
	
	interval atDDs[6][6]; half_array_multiply(at,DDs,atDDs);
	interval sstDDa[6][6]; half_array_multiply(sst,DDa,sstDDa);
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		DDx[i][j]= atDDs[i][j]+tDaDs[j][i]-tDaDs[i][j]-sstDDa[i][j]
				+ Daas[j]*Dssa[i];
 
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDx[i][j] = DDx[j][i];
	return 1;
	}

int secondDerive::setSqrtDelta(const double x[6],const double z[6],
	interval& sqrt_d,interval Dsqrt_d[6],interval DDsqrt_d[6][6])
	{
	interval d,Dd[6],DDd[6][6];
	::setDelta(x,z,d,Dd,DDd);
	return Dsqrt(d,Dd,DDd,sqrt_d,Dsqrt_d,DDsqrt_d);
	}

static int vor_126(const double x[6],const double z[6],
	const interval sqrt_d,const interval Dsqrt_d[6],
	const interval DDsqrt_d[6][6],
	interval DDv[6][6])
	{
	static const interval one("1");
	interval f,Df[6],DDf[6][6];
	interval c,Dc[6],DDc[6][6];
	interval u,Du[6],DDu[6][6];
	setF126(x,z,f,Df,DDf);
	setChi126(x,z,c,Dc,DDc);
	setU126(x,z,u,Du,DDu);
 
	interval a,Da[6],DDa[6][6];
	Leibniz::product(f,Df,DDf,c,Dc,DDc,a,Da,DDa);
 
	interval b,Db[6],DDb[6][6];
	Leibniz::product(u,Du,DDu,sqrt_d,Dsqrt_d,DDsqrt_d,b,Db,DDb);
 
	interval v,Dv[6],DDz[6][6];
	if (!Leibniz::quotient(a,Da,DDa,b,Db,DDb,v,Dv,DDz)) return 0;
	static const interval N48("48");
	static const interval r = one/N48;
	array_multiply(r,DDz,DDv); 
	return 1;
	}  // vor_126;


static int voronoiVolume(const double x[6],const double z[6],
	const interval sqrt_d,const interval Dsqrt_d[6],
	const interval DDsqrt_d[6][6],
	interval DDx[6][6])
	{
	interval DDt[6][6];
	double xx[6],zz[6]; // permutations of x,z;
	int i,j;
 
	if (!vor_126(x,z,sqrt_d,Dsqrt_d,DDsqrt_d,DDx)) return 0;
 
        // k is the inverse function of the reassignment.
	interval Ds[6],DDs[6][6];
	{
        int k[6] = {0,2,1,3,5,4}; 
	for (i=0;i<6;i++) { xx[i]=x[k[i]]; zz[i]=z[k[i]]; Ds[i]=Dsqrt_d[k[i]]; }
	for (i=0;i<6;i++) for (j=0;j<6;j++) DDs[i][j]=DDsqrt_d[k[i]][k[j]];
	if (!vor_126(xx,zz,sqrt_d,Ds,DDs,DDt)) return 0;
	for (i=0;i<6;i++) for (j=0;j<6;j++) 
		DDx[i][j] = DDx[i][j]+DDt[k[i]][k[j]];
	}
 
	{
        int k[6] = {2,1,0,5,4,3}; 
	for (i=0;i<6;i++) { xx[i]=x[k[i]]; zz[i]=z[k[i]]; Ds[i]=Dsqrt_d[k[i]]; }
	for (i=0;i<6;i++) { xx[i]=x[k[i]]; zz[i]=z[k[i]]; Ds[i]=Dsqrt_d[k[i]]; }
	for (i=0;i<6;i++) for (j=0;j<6;j++) DDs[i][j]=DDsqrt_d[k[i]][k[j]];
	if (!vor_126(xx,zz,sqrt_d,Ds,DDs,DDt)) return 0;
	for (i=0;i<6;i++) for (j=0;j<6;j++) 
		DDx[i][j]= DDx[i][j]+DDt[k[i]][k[j]]; // 2nd derivatives .
	}
	return 1;
	}

// 0.75 * vorAnalytic;
static int vorAnalytic34(const double x[6],const double z[6],
	const interval sqrt_d,const interval Dsqrt_d[6], 
	const interval DDsqrt_d[6][6],
	interval DDx[6][6],interval DDy[6][6])
	{
	int i,j;
	static const interval r = interval("-2.162708848552395278523"); // -3 doct
	if (!voronoiVolume(x,z,sqrt_d,Dsqrt_d,DDsqrt_d,DDx)) return 0;
	if (!secondDerive::setSolid(x,z,sqrt_d,Dsqrt_d,DDsqrt_d,DDy)) return 0;
	for (i=0;i<6;i++) for (j=0;j<6;j++) 
		DDx[i][j]= DDx[i][j]*r + DDy[i][j];
	return 1;
	}

int secondDerive::setVorAnalytic(const double x[6],const double z[6],
    double DD[6][6])
	{
	static const interval f3("1.33333333333333333333333333333");
    static const double d3=interMath::sup(f3);
    int i,j;
    interval sqrtd,Dsqrtd[6],DDsqrtd[6][6];
    interval DDy[6][6];
    interval DDx[6][6];
    if (!setSqrtDelta(x,z,sqrtd,Dsqrtd,DDsqrtd)) return 0;
    if (!vorAnalytic34(x,z,sqrtd,Dsqrtd,DDsqrtd,DDx,DDy)) return 0;
    interMath::up();
    for (i=0;i<6;i++) for (j=i;j<6;j++)
    DD[i][j]= d3*interMath::sup(interMath::max(DDx[i][j],-DDx[i][j]));
    for (i=0;i<6;i++) for (j=0;j<i;j++)
            DD[i][j] = DD[j][i];
    return 1;
	}



int secondDerive::setDihedral(const double x[6],const double z[6],double DDf[6][6])
	{
	int i,j;
	interval s,Ds[6],DDs[6][6];
	interval r,Dr[6],DDr[6][6];
	if (!setSqrtDelta(x,z,s,Ds,DDs)) return 0;
	if (!setDihedral(x,z,s,Ds,DDs,r,Dr,DDr)) return 0;
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		{
		DDf[i][j] = interMath::sup(interMath::max(DDr[i][j],-DDr[i][j]));
		}
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDf[i][j]= DDf[j][i];
	return 1;
	}

	//////////
	// Testing routines start here
	//
static int epsilonClose(double x,interval y,double epsilon)
	{
    if (interMath::abs(y-interval(x,x))>epsilon) 
		{
		cout << "close : " << interMath::abs(y-interval(x,x)) 
			  << " " << y << " " << x << endl<< flush;
		return 0;
		}
	return 1;
	}

static int epsilonClose(double f,double Df[6],double DDf[6][6],
	interval g,interval Dg[5],interval DDg[6][6],double epsilon)
    {
	int i,j;
    if (!epsilonClose(f,g,epsilon)) { cout << "*" << endl; return 0; }
    for (i=0;i<6;i++) if 
	 (!epsilonClose(Df[i],Dg[i],epsilon)) { cout << i << endl; return 0; }
    for (i=0;i<6;i++) for (j=0;j<6;j++) if 
	 (!epsilonClose(DDf[i][j],DDg[i][j],epsilon)) { cout << i <<" "<<j<<endl; return 0; }
    return 1;
    }

static double rand01()
    {
    static int w =0;
    if (w==0) { srand(time(0)); w = 1; }
    double u = double(rand());
    double v = double(/*stdlib.h*/RAND_MAX);
    return u/v;
    }



    /////////
    // The tests in secondDeriveTest are not designed to catch
    // errors in rounding modes, or other errors that at the machine epsilon
    // level.  These are coarser tests designed to detect
    // terms left out of the polynomials, misindexed a variables 
    // or some such thing.

void secondDerive::selfTest() {
	static const interval zero("0");
    cout << " -- loading derivative routines \n" << flush;
	double x[6]={4.01, 4.02, 4.03, 4.04, 4.05, 4.06};

	/*test setChi126*/ {
	// constants computed in Mathematica with lineInterval routine.
	double mf = 65.934;
	double Dmf[6] = {0.2428000000000061, 0.1225000000000058, 16.1182, 
    16.32069999999999, 16.28099999999999, -0.121699999999997};
	double DDmf[6][6] =    
	{{-8.08, -0.02999999999999936, 4.059999999999999, 0.0599999999999996, 4.019999999999999, 0.03}, 
    {-0.02999999999999936, -8.099999999999999, 4.059999999999999, 4.009999999999999, 0.03, 0.06}, 
    {4.059999999999999, 4.059999999999999, 0, 0, 0, -0.08999999999999985}, 
    {0.0599999999999996, 4.009999999999999, 0, 0, 0, 4.009999999999999}, 
    {4.019999999999999, 0.03000000000000024, 0, 0, 0, 4.019999999999999}, 
    {0.03, 0.06, -0.08999999999999985, 4.009999999999999, 4.019999999999999, -8.06}};
	interval f,Df[6],DDf[6][6];
	 ::setChi126(x,x,f,Df,DDf);
	if (!epsilonClose(mf,Dmf,DDmf,f,Df,DDf,1.0e-12))
		{
		cout << "Chi126 failed: " ;
		print (f,Df,DDf);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setU126*/ {
	// constants computed in Mathematica with lineInterval routine.
	double mf = 48.71989999999998;
	double Dmf[6] = {8.139999999999998, 8.099999999999999, 0, 0, 0, 7.939999999999999};
	double DDmf[6][6] =    {{-2, 2, 0, 0, 0, 2}, {2, -2, 0, 0, 0, 2}, 
    {0, 0, 0, 0, 0, 0}, {0, 0, 0, 0, 0, 0}, {0, 0, 0, 0, 0, 0}, 
    {2, 2, 0, 0, 0, -2}};
	interval f,Df[6],DDf[6][6];
	::setU126(x,x,f,Df,DDf);
	if (!epsilonClose(mf,Dmf,DDmf,f,Df,DDf,1.0e-12))
		{
		cout << "U126 failed: " ;
		print (f,Df,DDf);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setU135*/ {
	// constants computed in Mathematica with lineInterval routine.
	double mf = 48.72109999999999;
	double Dmf[6] = {8.14, 0, 8.059999999999998, 0, 7.979999999999998, 0};
	double DDmf[6][6] =    {{-2, 0, 2, 0, 2, 0}, {0, 0, 0, 0, 0, 0}, {2, 0, -2, 0, 2, 0}, 
    {0, 0, 0, 0, 0, 0}, {2, 0, 2, 0, -2, 0}, {0, 0, 0, 0, 0, 0}};
	interval f,Df[6],DDf[6][6];
	::setU135(x,x,f,Df,DDf);
	if (!epsilonClose(mf,Dmf,DDmf,f,Df,DDf,1.0e-12))
		{
		cout << "U135 failed: " ;
		print (f,Df,DDf);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setDelta*/ {
	// constants computed in Mathematica with lineInterval routine.
	double mf = 131.380797;
	double Dmf[6] = {16.56409999999999, 16.4029, 16.2401, 16.3199, 
    16.15989999999999, 15.99830000000001};
	double DDmf[6][6] =       
	{{-8.08, 4.03, 4.049999999999999, 0.05999999999999872, 4.029999999999999, 4.05}, 
	{4.03, -8.099999999999999, 4.069999999999999, 4.029999999999999, 0, 4.07}, 
    {4.049999999999999, 4.069999999999999, -8.119999999999999, 
     4.049999999999999, 4.069999999999999, -0.06000000000000049}, 
    {0.05999999999999872, 4.029999999999999, 4.049999999999999, 
     -8.019999999999999, 3.969999999999999, 3.989999999999999}, 
    {4.029999999999999, 0, 4.069999999999999, 
     3.969999999999999, -8.039999999999999, 4.01}, 
    {4.05, 4.07, -0.06000000000000049, 3.989999999999999, 4.01, -8.06}};
	interval f,Df[6],DDf[6][6];
	 ::setDelta(x,x,f,Df,DDf);
	if (!epsilonClose(mf,Dmf,DDmf,f,Df,DDf,1.0e-12))
		{
		cout << "Delta failed: " ;
		print (f,Df,DDf);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setDihedral*/ {
	// constants computed in Mathematica with lineInterval routine.
	double mf = 0;
	double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =       // absolute values of Mathematica data:
	 {{0.008363313633157451, 0.008383302773381245, 
     0.008250076013492677, 0.01077054498969235, 0.008474743772822185, 
     0.008341904494114842}, {0.008383302773381245, 0.001277263524111292, 
     0.03271689824683195, 0.01090598735249506, 0.01101316627580876, 
     0.01325163927245789}, {0.008250076013492675, 0.03271689824683195, 
     0.001228706462505481, 0.01079774461852813, 0.01325107206683709, 
     0.01101316627580876}, {0.01077054498969235, 0.01090598735249506, 
     0.01079774461852813, 0.01085080217485835, 0.01074442110953459, 
     0.01063697623355759}, {0.008474743772822188, 0.01101316627580876, 
     0.01325107206683709, 0.01074442110953459, 0.001454944164424718, 
     0.03239456361890094}, {0.008341904494114842, 0.01325163927245789, 
     0.01101316627580876, 0.01063697623355759, 0.03239456361890094, 
     0.001407409397727755}};
	interval f=zero,Df[6]={f,f,f,f,f,f},DDf[6][6];
	double DDg[6][6];
	 secondDerive::setDihedral(x,x,DDg);
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) DDf[i][j]=interval(DDg[i][j],DDg[i][j]);
	if (!epsilonClose(mf,Dmf,DDmf,f,Df,DDf,1.0e-12))
		{
		cout << "Dihedral failed: " ;
		print (f,Df,DDf);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setDihedral*/ {
	// constants computed in Mathematica with lineInterval routine.
	double mf = 1.229223064444068;
	double Dmf[6] = {0.05808963858208572, -0.05823559957162009, 
    -0.05881793762631476, 0.1747053643493189, -0.05736711261588325, 
    -0.0579480092805724};
	double DDmf[6][6] =       
	{{0.008363313633157451, -0.008383302773381245, 
     -0.008250076013492677, 0.01077054498969235, -0.008474743772822185, 
     -0.008341904494114842}, {-0.008383302773381245, -0.001277263524111292, 
     0.03271689824683195, -0.01090598735249506, -0.01101316627580876, 
     0.01325163927245789}, {-0.008250076013492675, 0.03271689824683195, 
     -0.001228706462505481, -0.01079774461852813, 0.01325107206683709, 
     -0.01101316627580876}, {0.01077054498969235, -0.01090598735249506, 
     -0.01079774461852813, -0.01085080217485835, -0.01074442110953459, 
     -0.01063697623355759}, {-0.008474743772822188, -0.01101316627580876, 
     0.01325107206683709, -0.01074442110953459, -0.001454944164424718, 
     0.03239456361890094}, {-0.008341904494114842, 0.01325163927245789, 
     -0.01101316627580876, -0.01063697623355759, 0.03239456361890094, 
     -0.001407409397727755}};
	interval f,Df[6],DDf[6][6];
	interval s,Ds[6],DDs[6][6];
	 secondDerive::setSqrtDelta(x,x,s,Ds,DDs);
	 secondDerive::setDihedral(x,x,s,Ds,DDs,f,Df,DDf);
	if (!epsilonClose(mf,Dmf,DDmf,f,Df,DDf,1.0e-9))
		{
		cout << "Dihedral' failed: " ;
		print (f,Df,DDf);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setDih2*/ {
	// constants computed in Mathematica with lineInterval routine.
	double mf = 1.232710638342055;
	double Dmf[6] = {-0.05830816732509592, 0.05845176570624949, 
    -0.0594685216951661, -0.05743718346519131, 0.1749230658223742, 
    -0.05859467983133313};
	double DDmf[6][6] =       
	{{-0.001123404207636204, -0.008531114747915529, 
     0.03275766698320512, -0.01091957737315987, -0.01102688985281611, 
     0.01326815222499805}, {-0.008531114747915529, 0.008443945879067538, 
     -0.008266244815639691, -0.008621711917258016, 0.01083702285350358, 
     -0.00835761522288147}, {0.03275766698320512, -0.008266244815639694, 
     -0.001027134142248158, 0.01326702351397333, -0.01081119975722912, 
     -0.01091957737315987}, {-0.01091957737315987, -0.008621711917258016, 
     0.01326702351397333, -0.001303019679439336, -0.01086432342892, 
     0.03243413183982465}, {-0.01102688985281611, 0.01083702285350359, 
     -0.01081119975722912, -0.01086432342892, -0.01075780980146961, 
     -0.01065023103774476}, {0.01326815222499805, -0.008357615222881467, 
     -0.01091957737315987, 0.03243413183982465, -0.01065023103774476, 
     -0.001208758007664149}};
	interval f,Df[6],DDf[6][6];
	interval s,Ds[6],DDs[6][6];
	 secondDerive::setSqrtDelta(x,x,s,Ds,DDs);
	 secondDerive::setDih2(x,x,s,Ds,DDs,f,Df,DDf);
	if (!epsilonClose(mf,Dmf,DDmf,f,Df,DDf,1.0e-9))
		{
		cout << "Dih2 failed: " ;
		print (f,Df,DDf);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setDih3*/ {
	// constants computed in Mathematica with lineInterval routine.
	double mf = 1.2362286230436;
	double Dmf[6] = {-0.05896443333921823, -0.05954244157664728, 
    0.05881306200320556, -0.05808947673791284, -0.05866606853987452, 
    0.1751404966904258};
	double DDmf[6][6] =       
	{{-0.0009184504467797998, 0.03279838504365084, 
     -0.008547453275827578, -0.01082463817106462, 0.01328407603344163, 
     -0.01104059637128659}, {0.03279838504365084, -0.0008707435131961496, 
     -0.008415810578114523, 0.0132835145377588, -0.01082463817106462, 
     -0.01093315050129961}, {-0.008547453275827578, -0.008415810578114523, 
     0.008527604205737668, -0.008637596596837754, -0.008506339658397171, 
     0.01090495198903783}, {-0.01082463817106462, 0.0132835145377588, 
     -0.008637596596837756, -0.001101047317770758, 0.03247364789813187, 
     -0.0108778278759341}, {0.01328407603344163, -0.01082463817106462, 
     -0.008506339658397171, 0.03247364789813187, -0.001054326241002047, 
     -0.01077118185113312}, {-0.01104059637128659, -0.01093315050129961, 
     0.01090495198903783, -0.0108778278759341, -0.01077118185113312, 
     -0.01066346936608415}};
	interval f,Df[6],DDf[6][6];
	interval s,Ds[6],DDs[6][6];
	 secondDerive::setSqrtDelta(x,x,s,Ds,DDs);
	 secondDerive::setDih3(x,x,s,Ds,DDs,f,Df,DDf);
	if (!epsilonClose(mf,Dmf,DDmf,f,Df,DDf,1.0e-9))
		{
		cout << "Dih3 failed: " ;
		print (f,Df,DDf);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setSolid*/ {
	// constants computed in Mathematica with lineInterval routine.
	double mf = 0;
	double Dmf[6] =  {0,0,0,0,0,0};
	double DDmf[6][6] =       
	{{0.006321458978741446, 0.01588396752235407, 
     0.01596013769388488, -0.01097367055453214, -0.006217557592196675, 
     -0.006114348640403384}, {0.01588396752235407, 0.006295938841760062, 
     0.01603484285307774, -0.006244184731994274, -0.01100078159336979, 
     -0.006039126451723204}, {0.01596013769388488, 0.01603484285307774, 
     0.006271763600984038, -0.006168317701392549, -0.006066467348789216, 
     -0.0110277916599308}, {-0.01097367055453214, -0.006244184731994274, 
     -0.006168317701392549, -0.01325486917206845, 0.01086490335967726, 
     0.01091932773033294}, {-0.006217557592196675, -0.01100078159336979, 
     -0.006066467348789216, 0.01086490335967726, -0.01326708020689638, 
     0.01097315073002304}, {-0.006114348640403384, -0.006039126451723204, 
     -0.0110277916599308, 0.01091932773033294, 0.01097315073002304, 
     -0.01327963677147607}};
	interval f=zero,Df[6]={f,f,f,f,f,f},DDf[6][6];
	interval s,Ds[6],DDs[6][6];
	 secondDerive::setSqrtDelta(x,x,s,Ds,DDs);
	 secondDerive::setSolid(x,x,s,Ds,DDs,DDf);
	if (!epsilonClose(mf,Dmf,DDmf,f,Df,DDf,1.0e-9))
		{
		cout << "Solid failed: " ;
		print (f,Df,DDf);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setSqrtDelta*/ {
	// constants computed in Mathematica with lineInterval routine.
	double mf = 11.46214626498894;
	double Dmf[6] =  {0.722556649385767, 0.7155248075180544, 
    0.708423170693838, 0.7119041941494427, 0.7049246984991068, 
    0.6978754078922687};
	double DDmf[6][6] =       
	{{-0.3980134266395165, 0.1306904272459834, 
     0.1320105408232354, -0.04226007049725636, 0.1313586423497506, 
     0.1326754560993297}, {0.1306904272459834, -0.3980036238159231, 
     0.1333175839690294, 0.1313554070679428, -0.04400494440984015, 
     0.1339760283627633}, {0.1320105408232354, 0.1333175839690294, 
     -0.3979938209923296, 0.132668920671104, 0.1339727285350904, 
     -0.04574981832242414}, {-0.04226007049725636, 0.1313554070679428, 
     0.132668920671104, -0.3940629858688967, 0.1293964599901556, 
     0.1307067224141014}, {0.1313586423497506, -0.04400494440984015, 
     0.1339727285350904, 0.1293964599901556, -0.3940726916346335, 
     0.1320041075660676}, {0.1326754560993297, 0.1339760283627633, 
     -0.04574981832242414, 0.1307067224141014, 0.1320041075660676, 
     -0.3940823978784881}};
	interval s,Ds[6],DDs[6][6];
	 secondDerive::setSqrtDelta(x,x,s,Ds,DDs);
	if (!epsilonClose(mf,Dmf,DDmf,s,Ds,DDs,1.0e-9))
		{
		cout << "SqrtDelta failed: " ;
		print (s,Ds,DDs);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setChi2over4uDelta */ {
	// constants computed in Mathematica with lineInterval routine.
	cout.precision(16);
	double mf =0;
	double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =       // absolute values of data:
	 {{0.002900593619379582, 0.008999531245737998, 
     0.0002903095202824827, 0.01541415188014938, 0.000175266553436075, 
     0.009178896693676442}, {0.008999531245737998, 0.002917241096743447, 
     0.0002908633130588728, 0.0001741204821707822, 0.01549054872713121, 
     0.009336743560276655}, {0.0002903095202824827, 0.0002908633130588728, 
     0.01545354994853072, 0.0001735454036735674, 0.0001741247584994103, 
     0.01556770672035573}, {0.01541415188014938, 0.0001741204821707822, 
     0.0001735454036735674, 0.01552860050683019, 0.0000588027441204772, 
     0.00005822763380499557}, {0.000175266553436075, 0.01549054872713121, 
     0.0001741247584994103, 0.0000588027441204772, 0.01560614339320554, 
     0.00005766101240632302}, {0.009178896693676442, 0.009336743560276655, 
     0.01556770672035573, 0.00005822763380499557, 0.00005766101240632302, 
     0.002973397416684484}};
	double DDx[6][6];
	interval s=zero,Ds[6]={s,s,s,s,s,s},DDs[6][6];
	 secondDerive::setChi2over4uDelta(x,x,DDx);
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) DDs[i][j]=interval(DDx[i][j],DDx[i][j]);
	if (!epsilonClose(mf,Dmf,DDmf,s,Ds,DDs,1.0e-12))
		{
		cout << "Chi2over4uDelta failed: " ;
		print (s,Ds,DDs);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setVorAnalytic */ {
	// constants computed in Mathematica with lineInterval routine.
	cout.precision(16);
	double mf =0;
	double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =       // absolute values of data:
	    {{0.04353277648516761, 0.002938575088868962, 0.002899978921543003, 
    0.01198312463504135, 0.002664704137289541, 0.002626619500685369}, 
   {0.002938575088868958, 0.04348983960076151, 0.002862426665875484, 
    0.002702576763206101, 0.0119144489576484, 0.002627318650262751}, 
   {0.002899978921543003, 0.002862426665875484, 0.04344822884131099, 
    0.002702964367146558, 0.002665787828920914, 0.01184563865055325}, 
   {0.01198312463504135, 0.002702576763206101, 0.002702964367146558, 
    0.005384594888795314, 0.004054718411768715, 0.004035252456129672}, 
   {0.002664704137289541, 0.0119144489576484, 0.002665787828920914, 
    0.004054718411768715, 0.005391003571976912, 0.004015808910221681}, 
   {0.002626619500685369, 0.002627318650262751, 0.01184563865055325, 
    0.004035252456129672, 0.004015808910221681, 0.005397402515344627}};
	double DDx[6][6];
	interval s=zero,Ds[6]={s,s,s,s,s,s},DDs[6][6];
	 secondDerive::setVorAnalytic(x,x,DDx);
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) 
		DDs[i][j]=interval(DDx[i][j],DDx[i][j]);
	if (!epsilonClose(mf,Dmf,DDmf,s,Ds,DDs,1.0e-12))
		{
		cout << "VorAnalytic failed: " ;
		print (s,Ds,DDs);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test Adihfactor*/{
	interval r,Dr,DDr;
	Adihfactor(4.1,4.1,interval("1.255"),r,Dr,DDr);
	if (!epsilonClose(0.0996154859996581,r,1.0e-14)||
		!epsilonClose(-0.0979123125455502,Dr,1.0e-14)||
		!epsilonClose(0.05644409964208811,DDr,1.0e-14))
		cout << " Adihfactor " << r << " " << Dr << " " << DDr << endl;
	}

	/*test setAdih */ {
	// constants computed in Mathematica with lineInterval routine.
	cout.precision(16);
	double mf =0;
	double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =
		 {{0.06004640331504228, 0.005090556359373819, 0.005165045370839407, 
    -0.01683395507298248, 0.004991118632279848, 0.005065416998339743}, 
   {0.005090556359373819, -0.0001387849846226313, 0.003554954897225364, 
    -0.001185023496277934, -0.001196669350828043, 0.0014398974979986}, 
   {0.005165045370839407, 0.003554954897225364, -0.0001335088682057223, 
    -0.001173262050119386, 0.001439835866532678, -0.001196669350828044}, 
   {-0.01683395507298248, -0.001185023496277934, -0.001173262050119386, 
    -0.001179027181590221, -0.00116746802074644, -0.00115579326829422}, 
   {0.004991118632279848, -0.001196669350828043, 0.001439835866532678, 
    -0.00116746802074644, -0.0001580914194092942, 0.003519930639868706}, 
   {0.005065416998339743, 0.0014398974979986, -0.001196669350828044, 
    -0.00115579326829422, 0.003519930639868706, -0.0001529263835803189}};
	interval s,Ds[6],DDs[6][6];
	interval n=zero,Dn[6]={n,n,n,n,n,n}; 
	interval f,Df[6],DDf[6][6];
	interval DDx1[6][6];
	secondDerive::setSqrtDelta(x,x,s,Ds,DDs);
	secondDerive::setDihedral(x,x,s,Ds,DDs,f,Df,DDf); 
	Adih(x[0],x[0],interval("1.255"), f,Df,DDf,DDx1); 
	if (!epsilonClose(mf,Dmf,DDmf,n,Dn,DDx1,1.0e-8))
		{
		cout << "Adih failed: " ;
		print (n,Dn,DDx1);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setVorVcNoQuoin */ {
	// constants computed in Mathematica with lineInterval routine.
	double z[6]={4.2,4.3,4.4,4.5,4.6,4.7}; // rad(z)>1.255, 
	cout.precision(16);
	double mf =0;
	double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =
		  {{0.05399742262145269, 0.001941109611880804, 0.002591451769354967, 
    -0.009341612836680926, 0.007105093042316984, 0.007324402654216028}, 
   {0.001941109611880805, 0.05402015824995872, 0.003150669397111228, 
    0.006969189493705773, -0.008721458819363622, 0.007351222717650264}, 
   {0.002591451769354965, 0.003150669397111225, 0.05422091663845037, 
    0.007035629668212111, 0.007200509217801438, -0.008091450771502836}, 
   {-0.009341612836680926, 0.006969189493705773, 0.007035629668212111, 
    0.00516319753220431, -0.004667265448268399, -0.00458015495504247}, 
   {0.007105093042316984, -0.008721458819363622, 0.007200509217801438, 
    -0.004667265448268399, 0.005267097722808903, -0.004487280153267206}, 
   {0.007324402654216028, 0.007351222717650264, -0.008091450771502833, 
    -0.004580154955042471, -0.004487280153267206, 0.005398344314989866}};
	interval DDx[6][6];
	 setVorVcNoQuoin(z,z,DDx);
	interval n=zero,Dn[6]={n,n,n,n,n,n}; 
	if (!epsilonClose(mf,Dmf,DDmf,n,Dn,DDx,1.0e-10))
		{
		cout << "VorVcNoQuoin failed: " ;
		print (n,Dn,DDx);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setVor1385NoQuoin */ {
	// constants computed in Mathematica.
	double z[6]={4.7,4.8,5.1,5.2,5.4,5.7}; // rad(z)>1.385, 
	cout.precision(16);
	double mf =0;
	double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =
	  {{0.0478546308290609, -0.002889268658288134, -0.001273118788492866, 
    -0.007541680741402377, 0.009956516628944605, 0.009948955415732298}, 
   {-0.002889268658288141, 0.04858100332439985, -0.0007824601321044857, 
    0.01008143637875229, -0.007004856760563882, 0.009969903466756662}, 
   {-0.00127311878849287, -0.0007824601321044823, 0.04906190095094674, 
    0.009932353325518896, 0.009810297045074584, -0.005359292348280169}, 
   {-0.007541680741402371, 0.01008143637875229, 0.009932353325518894, 
    0.008504386568552268, -0.007757250400015124, -0.00786228393249746}, 
   {0.009956516628944605, -0.007004856760563884, 0.009810297045074584, 
    -0.007757250400015124, 0.008544510896035715, -0.008006857876453842}, 
   {0.009948955415732301, 0.009969903466756662, -0.005359292348280169, 
    -0.00786228393249746, -0.008006857876453844, 0.009087438534120506}};
	interval DDx[6][6];
	 setVor1385NoQuoin(z,z,DDx);
	interval n=zero,Dn[6]={n,n,n,n,n,n}; 
	if (!epsilonClose(mf,Dmf,DDmf,n,Dn,DDx,1.0e-10))
		{
		cout << "Vor1385NoQuoin failed: " ;
		print (n,Dn,DDx);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setVorVc */ {
	// constants computed in Mathematica with lineInterval routine.
	double z[6]={4.2,4.3,4.4,4.5,4.6,4.7}; // rad(z)>1.255, 
	cout.precision(16);
	//double mf =0;
	//double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =       // absolute values of data:
		 {{0.04451022565404638, 0.003253033720076057, 0.002967145322222462, 
    0.009341612836680944, 0.000145986994096521, 0.0004158696512009301}, 
   {0.003253033720076055, 0.04411934782391634, 0.002752283828603631, 
    0.0001451969147139176, 0.008721458819363625, 0.0003321760267211591}, 
   {0.002967145322222464, 0.002752283828603629, 0.04383305357612751, 
    0.0002099334785566593, 2.749648354369998e-7, 0.008091450771502849}, 
   {0.009341612836680944, 0.0001451969147139176, 0.0002099334785566602, 
    0.002234984578078722, 0.004667265448268401, 0.004580154955042468}, 
   {0.0001459869940965228, 0.008721458819363627, 2.749648354369998e-7, 
    0.004667265448268401, 0.002261097147820291, 0.004487280153267206}, 
   {0.0004158696512009301, 0.0003321760267211582, 0.008091450771502849, 
    0.004580154955042467, 0.004487280153267206, 0.002276886164839177}};
	double DDx[6][6];
	interval s=zero,/*Ds[6]={s,s,s,s,s,s},*/  DDs[6][6];
	 secondDerive::setVorVc(z,z,DDx);
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) 
		{
		DDs[i][j]=interval(DDx[i][j],DDx[i][j]);
		if (interMath::inf(DDs[i][j])<DDmf[i][j]) 
		{
		cout << "VorVc failed: " ;
		cout << DDs[i][j] << " " << DDmf[i][j] << endl;
		error::message("Second derivatives failed to install properly");
		}
		}
	}

	/*test setVor1385 */ {
	// constants computed in Mathematica with lineInterval routine.
	double z[6]={4.7,4.8,5.1,5.2,5.4,5.7}; // rad(z)>1.385, 
	cout.precision(16);
	//double mf =0;
	//double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =       // absolute values of data:
		  {{0.03889899498521678, 0.007523143233144931, 0.007165317875469733, 
    0.007541680741402377, 0.0009378197311457164, 0.001164271193317731}, 
   {0.007523143233144937, 0.03911589910267211, 0.007425269314345619, 
    0.0005360683799675824, 0.007004856760563882, 0.001103923199169123}, 
   {0.007165317875469736, 0.007425269314345616, 0.03852289468931363, 
    3.746335451061677e-6, 0.0003551409556477469, 0.005359292348280169}, 
   {0.007541680741402371, 0.0005360683799675824, 3.746335451059942e-6, 
    0.001594711079555576, 0.007757250400015124, 0.00786228393249746}, 
   {0.0009378197311457164, 0.007004856760563884, 0.0003551409556477453, 
    0.007757250400015124, 0.001453346107969903, 0.008006857876453842}, 
   {0.001164271193317734, 0.001103923199169123, 0.005359292348280169, 
    0.00786228393249746, 0.008006857876453844, 0.001436156516679547}};
	double DDx[6][6];
	interval s=zero,/*Ds[6]={s,s,s,s,s,s},*/  DDs[6][6];
	 secondDerive::setVor1385(z,z,DDx);
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) 
		{
		DDs[i][j]=interval(DDx[i][j],DDx[i][j]);
		if (interMath::inf(DDs[i][j])<DDmf[i][j]) 
		{
		cout << "Vor1385 failed: " ;
		cout << DDs[i][j] << " " << DDmf[i][j] << endl;
		error::message("Second derivatives 1385 failed to install properly");
		}
		}
	}

	/*test setVorSqc */ {
	// constants computed in Mathematica with lineInterval routine.
	double z[6]={5.0,5.2,5.4,5.6,5.8,5.9}; // rad(z)>sqrt2,
	cout.precision(16);
	//double mf =0;
	//double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =       // absolute values of data:
		  {{0.03779865771267261, 0.008526248758379868, 0.008153674342434429, 
    0.006150356271165707, 0.002078061534485094, 0.001798102438960657}, 
   {0.008526248758379866, 0.03730624817730242, 0.008123471264883946, 
    0.001715235789950637, 0.005139529165605567, 0.001366146789444544}, 
   {0.008153674342434429, 0.008123471264883949, 0.03644883102152213, 
    0.001214466297812393, 0.00115110184311265, 0.004110707818849844}, 
   {0.006150356271165707, 0.001715235789950637, 0.001214466297812391, 
    0.0001456021154627295, 0.007967130062245022, 0.007945179163991298}, 
   {0.002078061534485092, 0.005139529165605567, 0.00115110184311265, 
    0.00796713006224502, 0.0001436042779515388, 0.008023844058987206}, 
   {0.001798102438960653, 0.001366146789444544, 0.004110707818849844, 
    0.007945179163991298, 0.008023844058987206, 0.0000378391999154605}};
	double DDx[6][6];
	interval s=zero,/*Ds[6]={s,s,s,s,s,s},*/  DDs[6][6];
	 secondDerive::setVorSqc(z,z,DDx);
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) 
		{
		DDs[i][j]=interval(DDx[i][j],DDx[i][j]);
		if (interMath::inf(DDs[i][j])<DDmf[i][j]) 
		{
		cout << "VorSqc failed: " ;
		cout << DDs[i][j] << " " << DDmf[i][j] << endl;
		error::message("Second derivatives failed to install properly");
		}
		}
	}

	/*test array_multiply */ {
	interval a[8];
	interval Df[6][6], adf[6][6];
	int i,j,k;
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		{ 
		double s;
		double t1 = rand01() - 0.5;
		double t2 = rand01()-0.5;
		if (t2<t1) { s=t1; t1=t2; t2=s; }
		Df[i][j]=interval(t1,t2);
		}
	for (k=0;k<8;k++)
		{ 
		double s;
		double t1 = rand01() - 0.5;
		double t2 = rand01()-0.5;
		if (t2<t1) { s=t1; t1=t2; t2=s; }
		a[8]=interval(t1,t2);
		}
	Df[0][0]=interval(3.0,4.0);
	Df[0][1]=interval(3.0,7.0);
	a[0]=interval(2.0,4.0);
	a[1]=interval(-1.0,4.0);
	for (k=0;k<8;k++)
	{
	array_multiply(a[k],Df,adf);
	for (i=0;i<6;i++) for (j=0;j<6;j++)
		if (!(a[k]*Df[i][j]==adf[i][j]))
			{
			cout.precision(16);
			cout << "array_mult failed : ";
			cout << a[k] << " * "
				 << Df[i][j] << " != "
				 << adf[i][j] << endl;
			error::message("array_mult failed ");
			}
	}
	}


	


}

