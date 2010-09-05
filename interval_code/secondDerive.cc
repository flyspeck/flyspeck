/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* ========================================================================== */

//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

// This and 3d.cc give essential bounds on the second derivatives
// of the key functions used in the Kepler conjecture.

// This file contains the six dimensional functions such as 
// dih,solid, etc. 

// This output will be fed into the inequality verifier to give good
// Taylor approximations to these functions.

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

void setDeltaFull(const double x[6],const double z[6],
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
	::setDeltaFull(x,z,f,Df,DDf);
	return 1;
	}

int secondDerive::setChi2over4uDelta(const double x[6],const double z[6],double DDf[6][6])
	{ // this + eta^2 126 is the circumradius squared of a simplex.
	int i,j;
	interval d,Dd[6],DDd[6][6];
	interval c,Dc[6],DDc[6][6];
	interval u,Du[6],DDu[6][6];
	::setDeltaFull(x,z,d,Dd,DDd);
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

// rho_x x = rho(sqrt x) 
// `!x. rho (sqrt x) = &1 + const1 * (sqrt x - &2) / (#0.52)`
static int rho_x_factor(double x,double z,interval& r,interval& Dr,
		interval& DDr)
	{
	static const interval one("1");
	static const interval two("2");
	static const interval four("4");
	static const interval _052("0.52");
	static const interval const1("0.17547965609182181051");
	double qu,qn;
	interMath::up(); qu = sqrt(z); interMath::down(); qn = sqrt(x);
	interval q = interval(qn,qu);
	interval xx = interval(x,z);
	interval xxq = xx*q;
	if ((interMath::inf(xxq)<=0.0)&& (interMath::sup(xxq)>=0.0)) return 0;
	r = one + const1 * (q - two) / _052;
	Dr =  const1 / (two * _052 * q);
	DDr = - const1 / (four * _052 * xxq);
	return 1;
	}

	////////
	//
	//
int secondDerive::setRhazim(double x,double z,
	const interval& d,const interval Dd[6],const interval DDd[6][6],
	interval DDc[6][6])
	{
	interval r,Dr,DDr;
	if (!(rho_x_factor(x,z,r,Dr,DDr))) return 0;
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
	//
int secondDerive::setRhazim2(double x,double z,
	const interval& d,const interval Dd[6],const interval DDd[6][6],
	interval DDc[6][6])
	// [x,z] is the second edge,
	// d,Dd,DDd are the output from setDih2 = dihedral2 & its derivatives
	// DDc output
	{
	interval r,Dr,DDr;
	if (!rho_x_factor(x,z,r,Dr,DDr)) return 0;
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
	//
int secondDerive::setRhazim3(double x,double z,
	const interval& d,const interval Dd[6],const interval DDd[6][6],
	interval DDc[6][6])
	// [x,z] is the third edge,
	// d,Dd,DDd are the output from setDih3 = dihedral3 & its derivatives
	// DDc output
	{
	interval r,Dr,DDr;
	if (!rho_x_factor(x,z,r,Dr,DDr)) return 0;
	int i,j;
	int pos=2; // n - 1.
	for (i=0;i<6;i++) for (j=i;j<6;j++)
		DDc[i][j] = r*DDd[i][j];
	for (i=0;i<6;i++) for (j=0;j<i;j++)
		DDc[i][j] = DDc[j][i];
	for (i=0;i<6;i++) DDc[pos][i] = DDc[pos][i] + Dr*Dd[i];
	for (i=0;i<6;i++) DDc[i][pos] = DDc[i][pos] + Dr*Dd[i];
	DDc[pos][pos] = DDc[pos][pos] + DDr*d;
	return 1;
	}




/*
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
*/

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
	::setDeltaFull(x,z,d,Dd,DDd);
	return Dsqrt(d,Dd,DDd,sqrt_d,Dsqrt_d,DDsqrt_d);
	}

int secondDerive::setAbsDihedral(const double x[6],const double z[6],double DDf[6][6])
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

	/*test setDeltaFull*/ {
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
	 ::setDeltaFull(x,x,f,Df,DDf);
	if (!epsilonClose(mf,Dmf,DDmf,f,Df,DDf,1.0e-12))
		{
		cout << "Delta failed: " ;
		print (f,Df,DDf);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setAbsDihedral*/ {
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
	 secondDerive::setAbsDihedral(x,x,DDg);
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

	/*test rho_x_factor*/{
	  // (D[1 + (sol0/Pi) * (Sqrt[x] - 2)/0.52, {x, 2}] /. x -> 4.1) // CForm
	interval r,Dr,DDr;
	rho_x_factor(4.1,4.1,r,Dr,DDr);
	if (!epsilonClose(1.0083844426471409,r,1.0e-14)||
	    !epsilonClose(0.08333002400566536,Dr,1.0e-14)||
	    !epsilonClose(-0.010162198049471386,DDr,1.0e-14))
		cout << " rho_x_factor " << r << " " << Dr << " " << DDr << endl;
	}

	/*test setRhazim */ {
	// constants computed in Mathematica.
	cout.precision(16);
	double mf =0;
	double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =
	  {{0.005245126669460297,-0.013297300244897132,-0.013213028939357187,
    0.025500292935778365,-0.013315639664370316,-0.013231634715242573},
   {-0.013297300244897134,-0.0012783404176458062,0.03274448270025619,
    -0.010915182469278466,-0.011022451757882776,0.013262812068349122},
   {-0.013213028939357187,0.03274448270025619,-0.0012297424163398379,
    -0.01080684847309495,0.013262244384502759,-0.011022451757882776},
   {0.025500292935778372,-0.010915182469278464,-0.01080684847309495,
    -0.010859950763607504,-0.010753480005687592,-0.010645944540188482},
   {-0.01331563966437032,-0.011022451757882776,0.013262244384502759,
    -0.010753480005687594,-0.0014561708650500508,0.032421876303758854},
   {-0.013231634715242576,0.013262812068349122,-0.011022451757882776,
    -0.010645944540188482,0.032421876303758854,-0.0014085960205759114}};
	interval s,Ds[6],DDs[6][6];
	interval n=zero,Dn[6]={n,n,n,n,n,n}; 
	interval f,Df[6],DDf[6][6];
	interval DDx1[6][6];
	secondDerive::setSqrtDelta(x,x,s,Ds,DDs);
	secondDerive::setDihedral(x,x,s,Ds,DDs,f,Df,DDf); 
	setRhazim(x[0],x[0], f,Df,DDf,DDx1); 
	if (!epsilonClose(mf,Dmf,DDmf,n,Dn,DDx1,1.0e-8))
		{
		cout << "rhazim failed: " ;
		print (n,Dn,DDx1);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setRhazim2 */ {
	// constants computed in Mathematica.
	cout.precision(16);
	double mf =0;
	double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =
	  {{-0.0011252973689814488,-0.013452420681453378,0.03281287022035823,
    -0.010937979050533644,-0.011045472373235487,0.013290511721913251},
   {-0.013452420681453378,0.005393357573760159,-0.013284754121167338,
    -0.013469872796702883,0.025575952434180323,-0.013302740261788173},
   {0.03281287022035823,-0.01328475412116734,-0.001028865069229974,
    0.013289381108784134,-0.0108294187965891,-0.01093797905053364},
   {-0.010937979050533644,-0.013469872796702885,0.013289381108784134,
    -0.0013052155288695245,-0.010882631992318677,0.03248878985538867},
   {-0.011045472373235487,0.025575952434180333,-0.010829418796589102,
    -0.010882631992318679,-0.010775938868048842,-0.010668178812536344},
   {0.013290511721913253,-0.013302740261788173,-0.01093797905053364,
    0.03248878985538867,-0.010668178812536346,-0.0012107950072768503}};
	interval s,Ds[6],DDs[6][6];
	interval n=zero,Dn[6]={n,n,n,n,n,n}; 
	interval f,Df[6],DDf[6][6];
	interval DDx1[6][6];
	secondDerive::setSqrtDelta(x,x,s,Ds,DDs);
	secondDerive::setDih2(x,x,s,Ds,DDs,f,Df,DDf); 
	setRhazim2(x[1],x[1], f,Df,DDf,DDx1); 
	if (!epsilonClose(mf,Dmf,DDmf,n,Dn,DDx1,1.0e-8))
		{
		cout << "rhazim2 failed: " ;
		print (n,Dn,DDx1);
		error::message("Second derivatives failed to install properly");
		}
	}

	/*test setRhazim3 */ {
	// constants computed in Mathematica.
	cout.precision(16);
	double mf =0;
	double Dmf[6] = {0,0,0,0,0,0};
	double DDmf[6][6] =
	  {{-0.00092077066270158,0.03288124126681869,-0.01352504317384853,
    -0.010851983683193324,0.013317634648200889,-0.011068487443228952},
   {0.03288124126681869,-0.0008729432104908573,-0.013441649866266996,
    0.013317071734051526,-0.010851983683193324,-0.010960770140396406},
   {-0.01352504317384853,-0.013441649866266996,0.005544159342143369,
    -0.01354187357424209,-0.013458747948172471,0.025653167416464027},
   {-0.010851983683193324,0.013317071734051526,-0.01354187357424209,
    -0.0011038288151572363,0.032555683760987324,-0.010905307757424315},
   {0.013317634648200889,-0.010851983683193322,-0.013458747948172475,
    0.032555683760987324,-0.0010569897102612775,-0.010798392320369683},
   {-0.011068487443228952,-0.010960770140396408,0.02565316741646404,
    -0.010905307757424317,-0.010798392320369683,-0.010690407728944524}};
	interval s,Ds[6],DDs[6][6];
	interval n=zero,Dn[6]={n,n,n,n,n,n}; 
	interval f,Df[6],DDf[6][6];
	interval DDx1[6][6];
	secondDerive::setSqrtDelta(x,x,s,Ds,DDs);
	secondDerive::setDih3(x,x,s,Ds,DDs,f,Df,DDf); 
	setRhazim3(x[2],x[2], f,Df,DDf,DDx1); 
	if (!epsilonClose(mf,Dmf,DDmf,n,Dn,DDx1,1.0e-8))
		{
		cout << "rhazim3 failed: " ;
		print (n,Dn,DDx1);
		error::message("Second derivatives failed to install properly");
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

/* 

(* Mathematica code used in testing *)
xE = {4.01, 4.02, 4.03, 4.04, 4.05, 4.06};

test2Data[f_] := Module[{},
       g[x__] := f @@ Sqrt[{x}];
      xsub = {x1 -> xE[[1]], x2 -> xE[[2]], x3 -> xE[[3]], x4 -> xE[[4]],
         x5 -> xE[[5]], x6 -> xE[[6]]};
      xxs = {x1, x2, x3, x4, x5, x6};
      rr[i_, j_] := D[g @@ xxs, {xxs[[i]], 1}, {xxs[[j]], 1}];
      ((Table[rr[i, j], {i, 1, 6}, {j, 1, 6}]) /. xsub) // CForm
      ];

 */
