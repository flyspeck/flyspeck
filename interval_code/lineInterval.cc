/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* ========================================================================== */

//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

#include <iomanip>
#include <iostream>
extern "C"
{
#include <math.h>
#include <stdlib.h>
#include <assert.h>
#include <float.h>
}
#include "error.h"
#include "interval.h"
#include "lineInterval.h"

domain::domain(double x1,double x2,double x3,double x4,double x5,double x6) {
	x[0]=x1; x[1]=x2; x[2]=x3; x[3]=x4; x[4]=x5; x[5]=x6; }

domain::domain(const double z[6])
	{ for (int i=0;i<6;i++) x[i]=z[i]; }

domain::domain() {}

interval lineInterval::partial(int i) const {
	static const interval zero("0");
	if ((i>-1)&&(i<6)) return Df[i];
	error::message("partial out of range"); 
	return zero;
	}

inline lineInterval operator*
	(const lineInterval& a,const lineInterval& b)
	{
	lineInterval temp;
	temp.f = b.f*a.f;
	int i;
	for (i=0;i<6;i++) temp.Df[i]= b.f*a.Df[i]+a.f*b.Df[i];
	return temp;
	}

inline lineInterval operator*
	(const lineInterval& b,const interval& a)
	{
	lineInterval temp;
	temp.f = b.f*a;
	for (int i=0;i<6;i++) temp.Df[i]= b.Df[i]*a;
	return temp;
	}

static lineInterval operator/
	(const lineInterval& b,const lineInterval& a)
	{
	static const interval one("1");
	lineInterval temp;
	interval ra = one/a.f;
	temp.f = b.f*ra;
	interval ra2 = ra*ra;
	for (int i=0;i<6;i++) temp.Df[i]= (b.Df[i]*a.f - a.Df[i]*b.f)*ra2;
	return temp;
	}

inline lineInterval operator+
	(const lineInterval& b,const lineInterval& a)
	{
	lineInterval temp;
	temp.f = b.f+a.f;
	int i;
	interMath::up();
	for (i=0;i<6;i++) temp.Df[i].hi=b.Df[i].hi+a.Df[i].hi;
	interMath::down();
	for (i=0;i<6;i++) temp.Df[i].lo=b.Df[i].lo+a.Df[i].lo;
	return temp;
	}

inline lineInterval operator-(const lineInterval& a)
	{
	lineInterval temp;
	temp.f = -a.f;
	int i;
	for (i=0;i<6;i++) temp.Df[i]=-a.Df[i];
	return temp;
	}

inline lineInterval operator-
	(const lineInterval& b,const lineInterval& a)
	{
	lineInterval temp;
	temp.f = b.f- a.f;
	int i;
	interMath::up();
	for (i=0;i<6;i++) temp.Df[i].hi=b.Df[i].hi-a.Df[i].lo;
	interMath::down();
	for (i=0;i<6;i++) temp.Df[i].lo=b.Df[i].lo-a.Df[i].hi;
	return temp;
	}

ostream &operator<< (ostream &stream,lineInterval x)
	{
	cout << "[" << x.f << ":" << flush;
	for (int i=0;i<6;i++) cout << x.Df[i] << " " << flush;
	cout << "]" << flush;
	return stream;
	}

lineInterval::lineInterval(interval a)
	{
	static const interval zero("0");
	f = a;
	for (int i=0;i<6;i++) Df[i]=zero;
	}

lineInterval::lineInterval()
	{
	static const interval zero("0");
	f = zero;
	for (int i=0;i<6;i++) Df[i]=zero;
	}

static lineInterval sqrt(lineInterval a)
	{
	static const interval two("2");
	static const interval one("1");
	lineInterval temp;
	temp.f = interMath::sqrt(a.f);
	interval rs = one/(two*temp.f);
	int i;
	for (i=0;i<6;i++) temp.Df[i]=rs*a.Df[i];
	return temp;
	}

static lineInterval atan(lineInterval a,lineInterval b) // atan(a/b);
	{
	static const interval one("1");
	lineInterval temp;
	temp.f = interMath::atan(a.f/b.f);
	interval rden = one/(a.f*a.f+b.f*b.f);
	int i;
	for (i=0;i<6;i++) temp.Df[i]= rden*(a.Df[i]*b.f-b.Df[i]*a.f);
	return temp;
	}

static void quotient2(const interval& a,const interval Da[2],
const interval& b,const interval Db[2],
	interval& v,interval Dv[2])
	{
	static const interval one("1");
	int i;
	v = a/b;
	interval b2 = one/(b*b);
	interval r[2];
	for (i=0;i<2;i++) r[i] = (Da[i]*b- a*Db[i]);
	for (i=0;i<2;i++) Dv[i] = r[i]*b2;
	}

static void product2(const interval& u,const interval Du[2],
	const interval& v,const interval Dv[2],
	interval& uv,interval Duv[2])
	{
	int i;
	uv = u*v;
	for (i=0;i<2;i++) Duv[i] = u*Dv[i] + v*Du[i];
	}

double ups_max(double x1,double x2,double x6) {
  interMath::up();
  return  (-x1)*x1+(-x2)*x2+(-x6)*x6+2.0*(x1*x2+x2*x6+x6*x1);
}

static lineInterval U126(double x1,double x2,double x6)
	{
	lineInterval t;
	interMath::down();
	t.f.lo = (-x1)*x1+(-x2)*x2+(-x6)*x6+2.0*(x1*x2+x2*x6+x6*x1);
	t.Df[0].lo = 2.0*(-x1+x2+x6);
	t.Df[1].lo = 2.0*(+x1-x2+x6);
	t.Df[5].lo = 2.0*(+x1+x2-x6);
	t.Df[2].lo = 0.0;
	t.Df[3].lo = 0.0;
	t.Df[4].lo = 0.0;
	interMath::up();
	t.f.hi = (-x1)*x1+(-x2)*x2+(-x6)*x6+2.0*(x1*x2+x2*x6+x6*x1);
	t.Df[0].hi = 2.0*(-x1+x2+x6);
	t.Df[1].hi = 2.0*(+x1-x2+x6);
	t.Df[5].hi = 2.0*(+x1+x2-x6);
	t.Df[2].hi = 0.0;
	t.Df[3].hi = 0.0;
	t.Df[4].hi = 0.0;
	return t;
	}

 lineInterval linearization::ups_126(const domain& x) 
	{
	double x1,x2,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x6 = x.getValue(5);
	return U126(x1,x2,x6);
	}

lineInterval linearization::delta(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	lineInterval t;
	interMath::up();
	t.f.hi =   x3*(x1 + x2 + x4 + x5)*x6 + x2*x5*(x1 + x3 + x4 + x6) + 
	   x1*x4*(x2 + x3 + x5 + x6);

	double tlo = (x2*x3+x5*x6)*x4 + x1*(x3*x5 + x2*x6) +
	   x3*(x3 + x6)*x6 + x2*x5*(x2 + x5) + x1*x4*(x1 + x4);

	t.Df[0].hi= (-x1)*x4 + x2*x5 +(-x3)*x5 +(-x2)*x6 + x3*x6 +
            x4*(x2 + x3 + x5 + x6) + x4*(-x1)+x4*(-x4);
        t.Df[1].hi=  x1*x4 + (- x3)*x4 +(- x2)*x5 +(- x1)*x6 + x3*x6 +
                x5*(x1 + x3 + x4  + x6)+ x5*(-x2)+x5*(-x5);
        t.Df[2].hi= x1*x4 +(- x2)*x4 +(- x1)*x5 + x2*x5 +(- x3)*x6 +
                (x1 + x2 + x4 + x5 )*x6+ x6*(-x3) + x6*(-x6);
        t.Df[3].hi= (-x2)*x3 +(- x1)*x4 + x2*x5 + x3*x6 +(- x5)*x6 +
                x1*(-x1) + x1*(-x4) + x1*(x2 + x3 + x5 + x6);
        t.Df[4].hi=  (-x1)*x3 + x1*x4 +(- x2)*x5 + x3*x6 +(- x4)*x6 +
                x2*(-x2) + x2*(-x5)+ x2*(x1 + x3 + x4 + x6);
        t.Df[5].hi= (-x1)*x2 + x1*x4 + x2*x5 +(-x4)*x5 +
                x3*(-x3) + x3*(-x6)+ x3*(x1 + x2 + x4 + x5 ) +(-x3)*x6;
 
	interMath::down();
	t.f.lo =   x3*(x1 + x2 + x4 + x5)*x6 + x2*x5*(x1 + x3 + x4 + x6) + 
	   x1*x4*(x2 + x3 + x5 + x6) - tlo;
	double thi = (x2*x3+x5*x6)*x4 + x1*(x3*x5 + x2*x6) +
	   x3*(x3 + x6)*x6 + x2*x5*(x2 + x5) + x1*x4*(x1 + x4);
 
	t.Df[0].lo= (-x1)*x4 + x2*x5 +(-x3)*x5 +(-x2)*x6 + x3*x6 +
            x4*(x2 + x3 + x5 + x6) + x4*(-x1)+x4*(-x4);
        t.Df[1].lo=  x1*x4 + (- x3)*x4 +(- x2)*x5 +(- x1)*x6 + x3*x6 +
                x5*(x1 + x3 + x4  + x6)+ x5*(-x2)+x5*(-x5);
        t.Df[2].lo= x1*x4 +(- x2)*x4 +(- x1)*x5 + x2*x5 +(- x3)*x6 +
                (x1 + x2 + x4 + x5 )*x6+ x6*(-x3) + x6*(-x6);
        t.Df[3].lo= (-x2)*x3 +(- x1)*x4 + x2*x5 + x3*x6 +(- x5)*x6 +
                x1*(-x1) + x1*(-x4) + x1*(x2 + x3 + x5 + x6);
        t.Df[4].lo=  (-x1)*x3 + x1*x4 +(- x2)*x5 + x3*x6 +(- x4)*x6 +
                x2*(-x2) + x2*(-x5)+ x2*(x1 + x3 + x4 + x6);
        t.Df[5].lo= (-x1)*x2 + x1*x4 + x2*x5 +(-x4)*x5 +
                x3*(-x3) + x3*(-x6)+ x3*(x1 + x2 + x4 + x5 ) +(-x3)*x6;
	interMath::up();
	t.f.hi = t.f.hi - thi;
	return t;
	}

lineInterval linearization::delta_x4(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	lineInterval t;
	interMath::up();
	t.f.hi =  (-x2)*x3 +(- x1)*x4 + x2*x5 + x3*x6 +(- x5)*x6 +
                x1*(-x1) + x1*(-x4) + x1*(x2 + x3 + x5 + x6); 
        t.Df[0].hi = (-2.0)* x1 + x2 + x3 + (- 2.0)* x4 + x5 + x6;
	t.Df[1].hi = x1 + (- 1.0) * x3 + x5;
	t.Df[2].hi = x1 + (- 1.0) * x2 + x6;
	t.Df[3].hi = (-2.0) * x1;
	t.Df[4].hi = x1 + x2 + (-1.0) * x6;
	t.Df[5].hi = x1 + x3 + (-1.0)* x5;
	interMath::down();
	t.f.lo = (-x2)*x3 +(- x1)*x4 + x2*x5 + x3*x6 +(- x5)*x6 +
                x1*(-x1) + x1*(-x4) + x1*(x2 + x3 + x5 + x6); 
        t.Df[0].lo = (-2.0)* x1 + x2 + x3 + (- 2.0)* x4 + x5 + x6;
	t.Df[1].lo = x1 + (- 1.0) * x3 + x5;
	t.Df[2].lo = x1 + (- 1.0) * x2 + x6;
	t.Df[3].lo = (-2.0) * x1;
	t.Df[4].lo = x1 + x2 + (-1.0) * x6;
	t.Df[5].lo = x1 + x3 + (- 1.0)* x5;
	return t;
	}

static lineInterval f126
	(double x1,double x2,double ,double ,double ,double x6)
	{
	static const interval zero("0");
	lineInterval t;
	interMath::up();
	t.f.hi = x2*(x1+x6) + x1*(x2+x6) + (-x1)*x1 + (-x2)*x2;
	t.Df[0].hi= -2.0*x1+2.0*x2+x6;
	t.Df[1].hi= 2.0*x1-2.0*x2 +x6;
	t.Df[2]= zero;
	t.Df[3]= zero;
	t.Df[4]= zero;
	t.Df[5].hi = x1+x2;
	interMath::down();
	t.f.lo = x2*(x1+x6) + x1*(x2+x6) + (-x1)*x1 + (-x2)*x2;
	t.Df[0].lo= -2.0*x1+2.0*x2+x6;
	t.Df[1].lo= 2.0*x1-2.0*x2 +x6;
	t.Df[5].lo = x1+x2;
	return t;
	}

static lineInterval f135
	(double x1,double x2,double x3,double x4,double x5,double x6)
	{
	lineInterval s,t;
	s = f126(x1,x3,x2,x4,x6,x5);
	static int k[6]= {0,2,1,3,5,4};
	int i;
	for (i=0;i<6;i++) t.Df[i]=s.Df[k[i]];
	t.f = s.f;
	return t;
	}

static lineInterval f324
	(double x1,double x2,double x3,double x4,double x5,double x6)
	{
	lineInterval s,t;
	s = f126(x3,x2,x1,x6,x5,x4);
	static int k[6]= {2,1,0,5,4,3};
	int i;
	for (i=0;i<6;i++) t.Df[i]=s.Df[k[i]];
	t.f = s.f;
	return t;
	}

static lineInterval chi126_local
	(double x1,double x2,double x3,double x4,double x5,double x6)
	{
	lineInterval t;
	interMath::up();
	t.f.hi = x1*x2*x4 + x1*x2*x5 + x1*x3*x6 + x2*x3*x6 
		+ x1*x4*x6 + x2*x5*x6;
	double tlo =  x1*x1*x4 + x2*x2*x5 + 2*x1*x2*x6 + x3*x6*x6;
	t.Df[0].hi = 2.0*((-x1)*x4) + x2*x4 + x2*x5 
			+2.0*((-x2)*x6) + x3*x6 + x4*x6;
	t.Df[1].hi = x1*x4 + x1*x5 + 2.0*((-x2)*x5) 
			+ 2.0*((-x1)*x6) + x3*x6 + x5*x6;
	t.Df[2].hi = x1*x6 + x2*x6 + (-x6)*x6;
	t.Df[3].hi = (-x1)*x1 + x1*x2 + x1*x6;
	t.Df[4].hi = (-x2)*x2 + x1*x2 + x2*x6;
	t.Df[5].hi = 2.0*((-x1)*x2) + x1*x3 + x2*x3 + x1*x4 + x2*x5 
			+ 2.0*((-x3)*x6);
	interMath::down();
	t.f.lo = x1*x2*x4 + x1*x2*x5 + x1*x3*x6 + x2*x3*x6 
		+ x1*x4*x6 + x2*x5*x6 - tlo;
	double thi =  x1*x1*x4 + x2*x2*x5 + 2*x1*x2*x6 + x3*x6*x6;
	t.Df[0].lo = 2.0*((-x1)*x4) + x2*x4 + x2*x5 
			+2.0*((-x2)*x6) + x3*x6 + x4*x6;
	t.Df[1].lo = x1*x4 + x1*x5 + 2.0*((-x2)*x5) 
			+ 2.0*((-x1)*x6) + x3*x6 + x5*x6;
	t.Df[2].lo = x1*x6 + x2*x6 + (-x6)*x6;
	t.Df[3].lo = (-x1)*x1 + x1*x2 + x1*x6;
	t.Df[4].lo = (-x2)*x2 + x1*x2 + x2*x6;
	t.Df[5].lo = 2.0*((-x1)*x2) + x1*x3 + x2*x3 + x1*x4 + x2*x5 
			+ 2.0*((-x3)*x6);
	interMath::up();
	t.f.hi = t.f.hi - thi;
	return t;
	}

lineInterval linearization::chi126(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	return chi126_local(x1,x2,x3,x4,x5,x6);
	}

lineInterval linearization::chi324(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	lineInterval t,s;
	s = chi126_local(x3,x2,x1,x6,x5,x4);
	int k[6]={2,1,0,5,4,3};
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	t.f = s.f;
	return t;
	}


static lineInterval chi135
	(double x1,double x2,double x3,double x4,double x5,double x6)
	{
	lineInterval t,s;
	s = chi126_local(x1,x3,x2,x4,x6,x5);
	int k[6]={0,2,1,3,5,4};
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	t.f = s.f;
	return t;
	}

static lineInterval U135
	(double x1,double x3,double x5)
	{
	lineInterval s,t;
	s = U126(x1,x3,x5);
	int k[6]={0,2,1,3,5,4};
	for (int i=0;i<6;i++) t.Df[i]=s.Df[k[i]];
	t.f = s.f;
	return t;
	}

static lineInterval U324
	(double x3,double x2,double x4)
	{
	lineInterval s,t;
	s = U126(x3,x2,x4);
	int k[6]={2,1,0,5,4,3};
	for (int i=0;i<6;i++) t.Df[i]=s.Df[k[i]];
	t.f = s.f;
	return t;
	}

static lineInterval a
	(double x1,double x2,double x3,double x4,double x5,double x6)
	{
	lineInterval t;
	double y1u,y1n,y2u,y2n,y3u,y3n;
 
	interMath::up();
	y1u = sqrt(x1); y2u = sqrt(x2); y3u = sqrt(x3);
	double y123u = y1u*y2u*y3u;
 
	interMath::down();
	y1n = sqrt(x1); y2n = sqrt(x2); y3n = sqrt(x3);
	double y123n = y1n*y2n*y3n;
	double tx=1;
	if (y123u>/*float.h*/DBL_EPSILON) tx = 1.0/y123u;
	else { error::message("divide by zero in lineInterval a"); }
 
	interval yy1=interval(y1n,y1u),y2=interval(y2n,y2u),
		y3 = interval(y3n,y3u);
	interval X1 = interval(x1,x1),X2=interval(x2,x2),
		X3 = interval(x3,x3), X4=interval(x4,x4),
		X5 = interval(x5,x5), X6 = interval(x6,x6);
	interval v = yy1*(X2+X3-X4)+ y2*(X1+X3-X5) + y3*(X1+X2-X6);
	interval v0 = (X2+X3-X4)/yy1;
	interval v1 = (X1+X3-X5)/y2;
	interval v2 = (X1+X2-X6)/y3;
 
	interMath::up();
	double tz = 1.0; 
	if (y123n>/*float.h*/DBL_EPSILON) tz=1.0/y123n;
	else { error::message("divide by zero y123n"); }
	t.Df[0].hi = (y2u+y3u + x2*x3*tz + interMath::sup(v0)/2.0)/2.0;
	t.Df[1].hi = (y1u+y3u + x1*x3*tz + interMath::sup(v1)/2.0)/2.0;
	t.Df[2].hi = (y1u+y2u + x1*x2*tz + interMath::sup(v2)/2.0)/2.0;
	t.Df[3].hi = -y1n/2.0;
	t.Df[4].hi = -y2n/2.0;
	t.Df[5].hi = -y3n/2.0;
	t.f.hi = y123u + interMath::sup(v)/2.0;
 
	interMath::down();
	t.Df[0].lo = (y2n+y3n + x2*x3*tx + interMath::inf(v0)/2.0)/2.0;
        t.Df[1].lo = (y1n+y3n + x1*x3*tx + interMath::inf(v1)/2.0)/2.0;
        t.Df[2].lo = (y1n+y2n + x1*x2*tx + interMath::inf(v2)/2.0)/2.0;
	t.Df[3].lo = -y1u/2.0;
	t.Df[4].lo = -y2u/2.0;
	t.Df[5].lo = -y3u/2.0;
	t.f.lo = y123n + interMath::inf(v)/2.0;
	return t;
	}
	
//	deltaX4 := partial delta/partial x4.
lineInterval deltaX4(double x1,double x2,double x3,double x4,double x5,double x6)
	{
	lineInterval t;
	interMath::up();
	t.f.hi = x2*x5 + x3*x6 + x1*(x2 + x3 + x5 + x6);
	double tlo = x1*x1 + x2*x3 + 2.0*x1*x4 + x5*x6;
	t.Df[0].hi= +2.0*(-x1) + x2 + x3 + 2.0*(-x4) + x5 + x6;
	t.Df[1].hi= x1-x3+x5;
	t.Df[2].hi= x1-x2+x6;
	t.Df[3].hi= 2.0*(-x1);
	t.Df[4].hi= x1+x2-x6;
	t.Df[5].hi= x1+x3-x5;
	interMath::down();
	t.f.lo = x2*x5 + x3*x6 + x1*(x2 + x3 + x5 + x6)-tlo;
	double thi = x1*x1 + x2*x3 + 2.0*x1*x4 + x5*x6;
	t.Df[0].lo= +2.0*(-x1) + x2 + x3 + 2.0*(-x4) + x5 + x6;
	t.Df[1].lo= x1-x3+x5;
	t.Df[2].lo= x1-x2+x6;
	t.Df[3].lo= 2.0*(-x1);
	t.Df[4].lo= x1+x2-x6;
	t.Df[5].lo= x1+x3-x5;
	interMath::up();
	t.f.hi = t.f.hi - thi;
	return t;
	}

lineInterval linearization::dih(const domain& x)
	{
	static const interval four("4");
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static const interval pi2 = "1.5707963267948966192313216916";
	static lineInterval p = lineInterval(pi2);
	lineInterval ax = -deltaX4(x1,x2,x3,x4,x5,x6);
	double x14 = 4.0*x1;
	lineInterval t = lineInterval(interval(x14,x14));  
	t.Df[0]=four;
	lineInterval b2 = linearization::delta(x)*t;
	lineInterval b = sqrt(b2);
	if (! interMath::boundedFromZero(b.f)) { throw unstable::x; };
	return p + atan(ax,b);
	}

lineInterval linearization::dih2(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static int k[6] = {1,0,2,4,3,5};
	lineInterval s,t;
	s =dih(domain(x2,x1,x3,x5,x4,x6));
	t.f = s.f;
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	return t;
	}

lineInterval linearization::dih3(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static int k[6] = {2,1,0,5,4,3};
	lineInterval s,t;
	s =dih(domain(x3,x2,x1,x6,x5,x4));
	t.f = s.f;
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	return t;
	}

lineInterval linearization::dih4(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static int k[6] = {3,1,5,0,4,2};
	lineInterval s,t;
	s =dih(domain(x4,x2,x6,x1,x5,x3));
	t.f = s.f;
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	return t;
	}

lineInterval linearization::dih5(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static int k[6] = {1,3,5,4,0,2};
	lineInterval s,t;
	s =dih(domain(x5,x1,x6,x2,x4,x3));
	t.f = s.f;
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	return t;
	}

lineInterval linearization::dih6(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static int k[6] = {1,5,3,4,2,0};
	lineInterval s,t;
	s =dih(domain(x6,x1,x5,x3,x4,x2));
	t.f = s.f;
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	return t;
	}

/*implement y1 copied from taylorSimplex.cc */
static lineInterval lineSqrt(lineInterval a)
    {
    lineInterval temp;
	static const interval one("1");
	static const interval two("2");
    temp.f = interMath::sqrt(a.f);
    interval rs = one/(two*temp.f);
    int i;
    for (i=0;i<6;i++) temp.Df[i]=rs*a.Df[i];
    return temp;
    }

static lineInterval lineY1(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(0),x.getValue(0)));
	h.Df[0]=one;
	return lineSqrt(h);
	}

lineInterval linearization::rhazim(const domain& x)
	{
	  static const lineInterval one(interval::interval ("1"));
	  static const lineInterval two(interval::interval ("2"));
	  static const lineInterval const1(interval::interval("0.17547965609182181051"));
	  static const lineInterval _052(interval::interval("0.52"));
	lineInterval d = linearization::dih(x);
	// `!y. rho y = &1 + const1 *(y - &2) / (#0.52)`
	lineInterval rho = one + const1 * (lineY1(x) - two) / _052;
	return rho*d;
	}

lineInterval linearization::rhazim2(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static int k[6] = {1,0,2,4,3,5};
	lineInterval s,t;
	s =rhazim(domain(x2,x1,x3,x5,x4,x6));
	t.f = s.f;
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	return t;
	}

lineInterval linearization::rhazim3(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static int k[6] = {2,1,0,5,4,3};
	lineInterval s,t;
	s =rhazim(domain(x3,x2,x1,x6,x5,x4));
	t.f = s.f;
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	return t;
	}

lineInterval linearization::rhazim4(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static int k[6] = {3,1,5,0,4,2};
	lineInterval s,t;
	s =rhazim(domain(x4,x2,x6,x1,x5,x3));
	t.f = s.f;
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	return t;
	}

lineInterval linearization::rhazim5(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static int k[6] = {1,3,5,4,0,2};
	lineInterval s,t;
	s =rhazim(domain(x5,x1,x6,x2,x4,x3));
	t.f = s.f;
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	return t;
	}

lineInterval linearization::rhazim6(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static int k[6] = {1,5,3,4,2,0};
	lineInterval s,t;
	s =rhazim(domain(x6,x1,x5,x3,x4,x2));
	t.f = s.f;
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	return t;
	}

lineInterval linearization::solid(const domain& x)
	{
	static const interval two("2");
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	lineInterval ax = a(x1,x2,x3,x4,x5,x6)*two;
	lineInterval s = sqrt(delta(x));
	return atan(s,ax)*two;
	}

/*
lineInterval arclength_x_123(const domain&) {
  double x1,x2,x3;
  x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
  lineInterval t;
}
*/

lineInterval linearization::eta2_126(const domain& x)
	{	
	static const interval zero("0");
	double x1,x2,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); 
	x6 = x.getValue(5);
	lineInterval t;
	t.Df[2]=t.Df[3]=t.Df[4]=zero;
	interMath::up();
	t.f.hi = x1*x2*x6;
	t.Df[0].hi = x2*x6;
	t.Df[1].hi = x1*x6;
	t.Df[5].hi = x1*x2;
	interMath::down();
	t.f.lo = x1*x2*x6;
	t.Df[0].lo = x2*x6;
	t.Df[1].lo = x1*x6;
	t.Df[5].lo = x1*x2;
	return t/U126(x1,x2,x6);
	}

lineInterval linearization::eta2_135(const domain& x)
	{
	domain y(x.getValue(0),x.getValue(2),x.getValue(1),
			 x.getValue(3),x.getValue(5),x.getValue(4));
	lineInterval t = eta2_126(y);
	lineInterval u;
	u.f=t.f;
	static int k[6]={0,2,1,3,5,4};
	int i;
	for (i=0;i<6;i++) u.Df[i]=t.Df[k[i]];
	return u;
	}

lineInterval linearization::eta2_234(const domain& x)
	{
	domain y(x.getValue(3),x.getValue(1),x.getValue(5),
			 x.getValue(0),x.getValue(4),x.getValue(2));
	lineInterval t = eta2_126(y);
	lineInterval u;
	u.f=t.f;
	static int k[6]={3,1,5,0,4,2};
	int i;
	for (i=0;i<6;i++) u.Df[i]=t.Df[k[i]];
	return u;
	}

lineInterval linearization::eta2_456(const domain& x)
	{
	domain y(x.getValue(3),x.getValue(4),x.getValue(2),
			 x.getValue(0),x.getValue(1),x.getValue(5));
	lineInterval t = eta2_126(y);
	lineInterval u;
	u.f=t.f;
	static int k[6]={3,4,2,0,1,5};
	int i;
	for (i=0;i<6;i++) u.Df[i]=t.Df[k[i]];
	return u;
	}

static inline double pos(double x)
	{
	return (x>0.0 ? x : 0.0);
	}

static double chimin(   double x1,double x2,double x3,
                double x4,double x5,double x6)  // compute min;
        {
	interMath::down();
	// note that quantities in parentheses are positive on a 
	// simplex with acute angles.
        return x3*x6*pos(x4+x5-x6) + x2*x5*pos(x4-x5+x6)+x1*x4*pos(-x4+x5+x6)
               +2.0*(((-x4)*x5)*x6);
        }

/*
double edgeBound::chi234min(const domain& x0,const domain& z0)
	{
	double x[6],z[6];
	int i;
	for (i=0;i<6;i++) { x[i]=x0.getValue(i); z[i]=z0.getValue(i); }
	double q[8];
	interMath::down();
	if ((x[1]>x[2]+x[3])||(x[2]>x[3]+x[1])||(x[3]>x[1]+x[3]))
		{
		error::message("chi234min has been implemented only for top acute");
		}
	q[0]=chimin(x[4],x[5],x[0],x[1],x[2],x[3]);
	q[1]=chimin(x[4],x[5],x[0],x[1],x[2],z[3]);
	q[2]=chimin(x[4],x[5],x[0],x[1],z[2],x[3]);
	q[3]=chimin(x[4],x[5],x[0],x[1],z[2],z[3]);
	q[4]=chimin(x[4],x[5],x[0],z[1],x[2],x[3]);
	q[5]=chimin(x[4],x[5],x[0],z[1],x[2],z[3]);
	q[6]=chimin(x[4],x[5],x[0],z[1],z[2],x[3]);
	q[7]=chimin(x[4],x[5],x[0],z[1],z[2],z[3]);
	double temp = q[0];
	for (i=1;i<8;i++) if (q[i]<temp) temp = q[i];
	return temp;
	}
*/

lineInterval linearization::rad2(const domain& x)
	{
	static const interval four("4");
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	lineInterval c = chi126_local(x1,x2,x3,x4,x5,x6);
	return c*c/(U126(x1,x2,x6)*delta(x)*four) 
			+ eta2_126(domain(x1,x2,0,0,0,x6));
	}

static lineInterval permute
	(const lineInterval& r,int k1,int k2,int k3,int k4,int k5,int k6)
	{
	int i; 
	const int k[6]={k1,k2,k3,k4,k5,k6};
	lineInterval u;
	for (i=0;i<6;i++) u.Df[i]= r.Df[k[i]];
	u.f=r.f;
	return u;
	}

// double version.
static double delta
	(double x1,double x2,double x3,double x4,double x5,
	double x6)
	{
	return 
	 -(x2*x3*x4) - x1*x3*x5 - x1*x2*x6 - x4*x5*x6 + 
   x3*(x1 + x2 - x3 + x4 + x5 - x6)*x6 + 
   x2*x5*(x1 - x2 + x3 + x4 - x5 + x6) + x1*x4*(-x1 + x2 + x3 - x4 + x5 + x6);
	}

// double version.
static double deltasup
	(double x1,double x2,double x3,double x4,double x5,double x6)
	{
	interMath::up();
	return 
	((-x2)*x3)*x4 +((- x1)*x3)*x5 +((- x1)*x2)*x6 +((- x4)*x5)*x6 + 
	x3*(x1 + x2 + x4 + x5)*x6 +  (x3*(-x3-x6))*x6 +
	x2*x5*(x1 + x3 + x4 + x6) + x2*(x5*(-x2-x5)) +
	x1*x4*(x2 + x3 + x5 + x6)+ x1*(x4*(-x1-x4));
	}


// double version (there are no promises of accuracy here, especially if u is
// small 
static double dihedral
	(double x1,double x2,double x3,double x4,double x5,
	double x6)
	{
	static const double pi2= 1.57079632679489661923132169164;
	double t = -(-(x2*x3) - x1*x4 + x2*x5 + x3*x6 - x5*x6 + 
	 x1*(-x1 + x2 + x3 - x4 + x5 + x6));
	double u = x1*delta(x1,x2,x3,x4,x5,x6);
	if (u<1.0e-8) return 2.0*pi2; 
	t = t/(2.0*sqrt(u));
	return atan(t) + pi2;
	}

// double version returns zero if there is trouble
static double dihedralmin
	(double x1,double x2,double x3,double x4,double x5,
	double x6)
	{
	static const interval two("2");
	static const interval pi2("1.57079632679489661923132169164");
	lineInterval u = linearization::delta(domain(x1,x2,x3,x4,x5,x6));
	interval den = interMath::sqrt(u.f*interval(x1,x1))*two;
	interval num = -u.Df[3];
	if ((interMath::sup(den)<1.0e-2)&&(interMath::abs(num)<1.0e-2))
		return 0; // This is always a lower bound on dihedral.
	if (interMath::sup(den)<1.0e-2)
		{
		if (interMath::inf(den) < 0)
			{
			error::message("negative square root???");
			return 0;
			}
		if (interMath::inf(num) > 0)
			return interMath::inf(two*pi2 - interMath::atan(den/num));
		if (interMath::sup(num) < 0)
			return interMath::inf(-interMath::atan(den/num));
		return 0;
		}
	if (interMath::inf(den)<1.0e-8) return 0;
	return interMath::inf(pi2+interMath::atan(num/den));
	}

// double version returns pi if there is trouble
static double dihedralmax
	(double x1,double x2,double x3,double x4,double x5,
	double x6)
	{
	static const interval two("2");
	static const interval pi2("1.57079632679489661923132169164");
	static const double pi_ub = 3.14159265359; // > pi. This is always an upper bound on dihedral.
	lineInterval u = linearization::delta(domain(x1,x2,x3,x4,x5,x6));
	interval den = interMath::sqrt(u.f*interval(x1,x1))*two;
	interval num = -u.Df[3];
	if ((interMath::sup(den)<1.0e-2)&&(interMath::abs(num)<1.0e-2))
	  return pi_ub;
	if (interMath::sup(den)<1.0e-2)
		{
		if (interMath::inf(den) < 0)
			{
			error::message("dihedralmax. negative square root???");
			return pi_ub;
			}
		if (interMath::inf(num) > 0)
			return interMath::sup(two*pi2 - interMath::atan(den/num));
		if (interMath::sup(num) < 0)
			return interMath::sup(-interMath::atan(den/num));
		return pi_ub;
		}
	if (interMath::sup(den)<1.0e-8) return pi_ub;
	return interMath::sup(pi2+interMath::atan(num/den));
	}


static double edge_flat2_x(double x1,double x2,double x3,double x5,double x6) {
  // Solve[DeltaX[x1,x2,x3,x4,x5,x6]==0,x4].  gives an upper bound.
  // same as `edge_flat2_x` in sphere.hl.
  double ua = ups_max(x1,x3,x5);
  double ub = ups_max(x1,x2,x6);
  if (ua < 0.0 || ub < 0.0) { throw unstable::x; }
  interMath::up();
  return 
    ((-x1)*x1 + x1*x2 + x1*x3 + (- x2)*x3 + x1*x5 + x2*x5 + x1*x6 + x3*x6 + (-    x5)*x6 
     + sqrt( ua * ub   ))/(2.0*x1);
}

/* uses monotonicity. 
 throws unstable::x.
 quad cluster labeling of variables.
 The formula comes form solving 
   theta == Dihedral[Sqrt[x1], Sqrt[x2], Sqrt[x3], Sqrt[x4], Sqrt[x5], Sqrt[x6]]
   for x4.

  This is a trigonometric calculation of the "Enclosed" function in mathematica.
  or enclosed in sphere.hl.  The edge numbers y1,..y9 are the
  standard quad cluster numbering (with y1 y2 y3 y7 connected to the origin,
  and y4 diagonal, and y5, y6, y8, y9 top edges).

  xcd = cd^2, cd = enclosed y1 y5 y6 y4 y2 y3 y7 y8 y9,   yi^2 = xi.
*/
static double x4_diag_max_simple(double xcd,
			    double x1,double x2,double x3,double x5,double x6,double x7,
			  double x8min,double x8max,double x9min,double x9max) {
  static interval pi("3.141592653589793238462");
  static interval two("2.0");
  double th1 = dihedralmax(x1,x2,x7,x9max,xcd,x6);
  double th2 = dihedralmax(x1,x3,x7,x8max,xcd,x5);
  int reflex = 0;
  interMath::up();
  double theta = th1 + th2;
  if (theta > interMath::sup(pi)) { 
    reflex = 1; 
    th1 = dihedralmin(x1,x2,x7,x9min,xcd,x6);
    th2 = dihedralmin(x1,x3,x7,x8min,xcd,x5);
    interMath::up();
    theta = 2.0* interMath::sup(pi) + (-1.0 * th1) + (-1.0 * th2);
    if (theta > interMath::inf(pi)) { return edge_flat2_x(x1,x2,x3,     x5,x6);       };
  }
  interMath::down();
  double ctheta = cos(theta);
  interMath::up();
  double mct = - ctheta;
  if (mct < 0.0) { mct = 0.0; }  // mct <0 <=> theta < pi/2.  This effectively makes theta at least pi/2.
  double u126 = ups_max(x1,x2,x6);
  double u135 = ups_max(x1,x3,x5);
  if (u126 < 0.0 || u135 < 0.0) { throw unstable::x; }
  double f = mct * sqrt(u126 * u135);
  double b = (- x1)*x1 + x1*x2 + x1*x3 + (- x2)*x3 + x1*x5 + 
    x2*x5 + x1*x6 + x3*x6 + (- x5)*x6;
    return (b + f) / (2.0 * x1);  
    // - 2 x1 x4 + b = - f =  cos(theta) * sqrt(u126 * u135);
    // theta = arccos( (- 2 x1 x4 + b) / sqrt (u126 * u135) );
}

/*

  x4_diag_max takes the angle along the edge x1.
  Here we  take the angle along the cross-diag.  This calls for some unpleasant reindexing.

  The implicit monotonicity results hold for quad clusters.  Beyond that caveat emptor.
  (But I believe it should hold for all nonreflexive quads.)
  The upper bound monotonicity is stating that a diagonal of a skew triangle increases if
   the other diagonal has fixed length and one edge of the quad increases.
   So x2 x3 x5 x6 are as large as possible.

   The lower bound monotonicity are on the three edges that form the triangle of
   edges that do not meet the edge x4.

   The two edges x8 x9 
   that vary between lower and upper bounds are the two edges opposite
   the edge x1 used to compute dihedral angles.
 */
double edgeBound::x4_diag_max(double xcd_lb,
						const double xA[6],const double xB[6],
						 const double zA[6],const double zB[6])  {
  double x1 = xcd_lb;
  double x2 =zA[5];
  double x3 =zA[4];
  double x5 =zB[4];
  double x6= zB[5];
  double x7 = xA[0];
  double x8min=xA[2];
  double x8max=zA[2];
  double x9min=xA[1];
  double x9max=zA[1];
  double xcd=xB[0];
  return x4_diag_max_simple(xcd,
			    x1,x2,x3,x5,x6,x7,
		     x8min,x8max,x9min,x9max);
}

// 
double edgeBound::x4_upper_from_top_delta(double xcd_lb,
						 const double zA[6],const double zB[6]) {
  double x1=xcd_lb;
  double x2=zA[4];
  double x3=zA[5];
  double x5=zB[5];
  double x6=zB[4];
  // We should add some  preconditions make the implicit monotonicity lemmas easier to prove.
  return edge_flat2_x(x1,x2,x3,x5,x6);
}

double edgeBound::x3_upper_from_delta(double deltamin, double x1,double x2)  {
  // Solve[DeltaX[2, 2, 2, x1, x2, x3] == deltamin, x3] // Last // InputForm
  interMath::up();
  double discr = (-8.0)*deltamin + 64.0*x1*x2 + ((- 8.0*x1)*x1)*x2 + (( - 8.0*x1)*x2) * x2 + x1*x1*x2*x2;
  if (discr < 0.0) { throw unstable::x; };
  double sqrtd = sqrt(discr);
  return (4.0*x1 + 4.0*x2 + (-  x1)*x2 +  sqrtd)/4.0;
}

double edgeBound::x3_lower_from_delta(double deltamax, double z1,double z2)  {
  // adapted from x3_upper_from_delta
  interMath::down();
  double discr = (-8.0)*deltamax + 64.0*z1*z2 + ((- 8.0*z1)*z1)*z2 + (( - 8.0*z1)*z2) * z2 + z1*z1*z2*z2;
  if (discr < 0.0) { throw unstable::x; }
  double sqrtd = sqrt(discr);
  return (4.0*z1 + 4.0*z2 + (-  z1)*z2 +  sqrtd)/4.0;
}

double edgeBound::x4_lower_from_rad2(double z[6]) {
  double x1 = z[0]; double x2 = z[1]; double x3 = z[2]; double x5 = z[4]; double x6 = z[5];
  /* numrad2 = 2 - (Rad @@ 
    Sqrt[{x1, x2, x3, x4, x5, x6}])^2 // Together // Numerator;
    Solve[numrad2 == 0, x4] // Last // InputForm */
  interMath::up();
  double aup =  (8*x1  + (- x1) * x1);
  double bup =    (8*x1*x1  + (- 8*x1)*x2 - 8*x1*x3 + 8*x2*x3 
		     + (-        8*x1)*x5 + (- 8*x2)*x5 + 2*x1*x2*x5 + (- 8*x1)*x6 
		     + (-      8*x3)*x6 + 2*x1*x3*x6 + 8*x5*x6);
  double cup =  ((-8*x1)*x2)*x5 + 8*x2*x2*x5 + 
    8*x1*x3*x5 + ((- 8*x2)*x3)*x5 + 8*x2*x5*x5 + (((- x2)*x2)*x5)*x5 + 
    8*x1*x2*x6 + ((- 8*x1)*x3)*x6 + ((- 8*x2)*x3)*x6 + 
    8*x3*x3*x6 + ((- 8*x2)*x5)*x6 + ((- 8*x3)*x5)*x6 + 
    2*x2*x3*x5*x6 + 8*x3*x6*x6 + (((- x3)*x3)*x6)*x6; 

  interMath::down();
  double bdown =    (8*x1*x1  + (- 8*x1)*x2 - 8*x1*x3 + 8*x2*x3 
		     + (-        8*x1)*x5 + (- 8*x2)*x5 + 2*x1*x2*x5 + (- 8*x1)*x6 
		     + (-      8*x3)*x6 + 2*x1*x3*x6 + 8*x5*x6);
  if (bdown * bup < 0.0)  { throw unstable::x; }
  double b = ( (bdown > 0.0) ? bdown : bup );
  double discr = b * b + ( - 4 * cup) * aup;
  if (discr < 0.0) { throw unstable::x; };
  return   (- bup +  sqrt(discr  ))/(2.0 * aup );

}

double edgeBound::x4_upper_from_rad2(double x[6]) {
  double x1 = x[0]; double x2 = x[1]; double x3 = x[2]; double x5 = x[4]; double x6 = x[5];
  /* reverse rounding from x4_lower... */
  interMath::down();
  double adown =  (8*x1  + (- x1) * x1);
  double bdown =    (8*x1*x1  + (- 8*x1)*x2 - 8*x1*x3 + 8*x2*x3 
		     + (-        8*x1)*x5 + (- 8*x2)*x5 + 2*x1*x2*x5 + (- 8*x1)*x6 
		     + (-      8*x3)*x6 + 2*x1*x3*x6 + 8*x5*x6);
  double cdown =  ((-8*x1)*x2)*x5 + 8*x2*x2*x5 + 
    8*x1*x3*x5 + ((- 8*x2)*x3)*x5 + 8*x2*x5*x5 + (((- x2)*x2)*x5)*x5 + 
    8*x1*x2*x6 + ((- 8*x1)*x3)*x6 + ((- 8*x2)*x3)*x6 + 
    8*x3*x3*x6 + ((- 8*x2)*x5)*x6 + ((- 8*x3)*x5)*x6 + 
    2*x2*x3*x5*x6 + 8*x3*x6*x6 + (((- x3)*x3)*x6)*x6; 

  interMath::up();
  double bup =    (8*x1*x1  + (- 8*x1)*x2 - 8*x1*x3 + 8*x2*x3 
		     + (-        8*x1)*x5 + (- 8*x2)*x5 + 2*x1*x2*x5 + (- 8*x1)*x6 
		     + (-      8*x3)*x6 + 2*x1*x3*x6 + 8*x5*x6);
  if (bdown * bup < 0.0)  { throw unstable::x; }
  double b =( (bup > 0.0) ? bup : bdown );
  double discr = b * b + (- 4 * cdown) * adown;
  if (discr < 0.0) { throw unstable::x; };
  return   (- bdown +  sqrt( discr ))/(2.0 * adown );

}




// Assuming opposite edges to x3 on 3 simplices have lengths at least
// x0min,x3min,x0pmin, calculate the Excess angle over 2pi.
// If one of the terms is "greater than pi" (as an azimuth angle),
// then the geometric excess will be even greater than the return
// value.
/*
static double ExcessAngle
	(double x0min,double x0pmin,double x1,double x2,double x3min,
	double x4,double x4p,double x5,double x5p)
	{
	static const double pi2=6.28318530717958647692528676656;
	return dihedral(x3min,x4,x2,x0min,x1,x5)+
	  dihedral(x3min,x4,x4p,x3min,x5p,x5)+
	  dihedral(x3min,x4p,x2,x0pmin,x1,x5p)-pi2;
	}
*/

// Same as ExcessAngle but use careful intervals rather than 
// floating point.
/*
static double ExcessAngleInf
	(double x0min,double x0pmin,double x1,double x2,double x3min,
	double x4,double x4p,double x5,double x5p)
	{
	static const interval pi2("6.28318530717958647692528676656");
	double d1=dihedralmin(x3min,x4,x2,x0min,x1,x5),
	  d2= dihedralmin(x3min,x4,x4p,x3min,x5p,x5),
	  d3 = dihedralmin(x3min,x4p,x2,x0pmin,x1,x5p);
	interMath::down();
	return d1+d2+d3-interMath::sup(pi2);
	}
*/

// f(x1):=a0 + a1 x1 + a2 x1^2 + a3 x1^3 = delta(x1,x2,x3,x1,x5,x6);
// return value = 0 means effort failed and x1 return value is
//	undefined.
// return value = 1 means x1 is set to an upper bound
// on the largest real root of f(x1).
static int x1supDELTA
	(double x2,double x3,double x5,double x6,double& x1)
	{
	double sT = 6.3344; // added 5/2/98. was 6.3001, but for dodec....
	x1 = 8.0;
	if ((x2<4.0)||(x3<4.0)||(x5<4.0)||(x6<4.0)
		||(x2>sT)||(x3>sT)||(x5>sT)||(x6>sT))
		return 0;
	double a0 =  (x2 - x3 + x5 - x6)*(-(x2*x5) + x3*x6);
	double a1 =  -(x2*x3) + 2*x2*x5 - x3*x5 - x2*x6 + 2*x3*x6 - x5*x6;
	double a2 =  x2 + x3 + x5 + x6;
	double a3 = -2.0;
	double t = 12.9; // 12.9 > 2*sT, so it is an upper bd on x1.
	double t2;
	double den;
	for (int i=0;i<5;i++) // Newton's method
		// partial convergents are upper bounds because the
		// second derivative is negative (when x1>x2,x3,x5,x6).
		// (f''(x1) = -12x1+2x2+2x3+2x5+2x6)
		{
		t2 = t*t;
		den = (a1+2.0*a2*t+3.0*a3*t2);
		if ((den<DBL_EPSILON)&&(den>-DBL_EPSILON)) return 0;
		t = t - (a0+a1*t+a2*t2+a3*t2*t)/den;
		}
	x1 = t+ 1.0e-8; // add an epsilon for safe measure;
	// We need to keep x1>x2,x3,x5,x6 :
	if (x1<7.9) return 0; 
	// now verify the result rigorously by computing delta.
	double tH= deltasup(x1,x2,x3,x1,x5,x6);
	if (tH>0.0) return 0;
	// Since f''<0, the largest root is that satisfying f'(x1)<0;
	double tD= a1+2.0*a2*x1+3.0*a3*x1*x1;
	if (tD>0.0) return 0;
	return 1;
	}

// return 1 if we successfully set x3max to an upper bound.
// proofed on Oct 30, 97. I believe its accuracy. It uses monotonicity lemmas.
/*
int edgeBound::shortDiagMax
	(double x0min,double x0pmin,double x1,double x2,double x3min,
	double& x3max,double x4,double x4p,double x5,double x5p)
	{
	if (x3min>x3max) error::message("inverted x3 in shortDiagMax");
	double t;
	if (x1supDELTA(x4,x5,x5p,x4p,t)) // x5p x4p swapped Oct 30, 1997
									 // was a bug because order is
									 // x2,x3,x5,x6, so 1st&3rd vars are opp!
		{
		if (t<= x3min) { x3max=t; return 1; }
		if (t< x3max) x3max = t;
		}
	if (dihedral(x3max,x2,x4,x0min,x5,x1)+dihedral(x3max,x2,x4p,x0pmin,x5p,x1)
			< 3.14159)
		{
		// we won't do much better so get out fast with current max
		return 1;
		}
	double g0,g1;
	g1=ExcessAngle(x0min,x0pmin,x1,x2,x3max,x4,x4p,x5,x5p);
	if (g1<0.0) return 1;
	g0=ExcessAngle(x0min,x0pmin,x1,x2,x3min,x4,x4p,x5,x5p);
	if (g0>0.0)
		{
		double t0 = x3min-1.0e-10;
		if ((x3max>t0)&&(ExcessAngleInf(x0min,x0pmin,x1,x2,t0,x4,x4p,x5,x5p)>0))
			 { x3max=t0; return 1; }
		// This should happen only rarely:
		t0 = x3min+1.0e-4;
		if ((x3max>t0)&&(ExcessAngleInf(x0min,x0pmin,x1,x2,t0,x4,x4p,x5,x5p)>0))
			 {  x3max=t0; return 1; }
		// I don't ever expect to arrive here, but its ok if we do.
		}
	// now we have probably have mixed signs, approximate the root:
	double t0=x3min,t1=x3max;
	double tr,gr,th,gh;
	for (int i=0;i<4;i++) // numerical approximation to the root:
			// close in with secant and tangent(Newton).
	{
	if ((fabs(g1-g0)<1.e-14)) return 0;
	tr = t0 - g0*(t1-t0)/(g1-g0); // secant root;
	gr = ExcessAngle(x0min,x0pmin,x1,x2,tr,x4,x4p,x5,x5p);
	if (gr>0.0) { t1=tr; g1=gr; } else { t0=tr; g0 = gr; }
	th = t0+ 1.0e-6;
	gh =  ExcessAngle(x0min,x0pmin,x1,x2,th,x4,x4p,x5,x5p);
	if ((gh>0.0)&&(th<t1)) { t1 = th; g1=gh; }
	if ((fabs(gh-g0)<1.e-14)) return 0;
	tr = t0 - gh*(t0-th)/(g0-gh); // approx tangent root;
	if ((tr>t0)&&(tr<t1))
		{
		gr = ExcessAngle(x0min,x0pmin,x1,x2,tr,x4,x4p,x5,x5p);
		if (gr>0.0) { t1=tr; g1=gr; } else { t0=tr; g0 = gr; }
		}
	}
	if (t1+1.0e-5<x3max) x3max = t1+1.0e-05;
	// check that ExcessAngleInf(...) > 0 rigorously
	if ((deltasup(x3max,x2,x4,x0min,x5,x1)<=0.0)||
	    (deltasup(x3max,x2,x4p,x0pmin,x5p,x1)<=0.0)||
	    (deltasup(x3max,x4,x4p,x3max,x5p,x5)<=0.0)) return 1;
	if (ExcessAngleInf(x0min,x0pmin,x1,x2,x3max,x4,
		x4p,x5,x5p)<0.0) return 0;
	return 1;
	}
*/

int PositiveDelta2(const double x[6],const double z[6])
	// return 1 if Delta2>0, 0 otherwise.
	{
	//minimize f=Delta2.
	double x1=x[0],x2=x[1],x3=x[2],x4=x[3],x5=x[4],x6=x[5];
	double z1=z[0],z2=z[1],z3=z[2],z4=z[3],z5=z[4],z6=z[5];
	// f2  -2 x5 <0 
	x2=z2;
	int change=1;
	while (change)
	{
	change=0;
	// f1:
	if (x1!=z1)
		{
		interMath::up();
		if (z4+z5-x6<0) { x1=z1; change=1; }
		interMath::down();
		if (x4+x5-z6>0) { z1=x1; change=1; }
		}
	// f6:
	if (z6!=x6)
		{
		interMath::up();
		if (z3+z5-x1<0) { x6=z6; change=1; }
		interMath::down();
		if (x3+x5-z5>0) { z6=x6; change=1; }
		}
	// f4:
	if (z4!=x4)
		{
		interMath::up();
		if (z1+z5-x3<0) { x4=z4; change=1; }
		interMath::down();
		if (x1+x5-z3>0) { z4=x4; change=1; }
		}
	// f3:
	if (z3!=x3)
		{
		interMath::up();
		if (z5+z6-x4<0) { x3=z3; change=1; }
		interMath::down();
		if (x5+x6-z4>0) { z3=x3; change=1; }
		}
	// f5:
	if (z5!=x5)
		{
		interMath::up();
		if (z1 + (-2)*x2 + z3 + z4 +(-2)*x5 + z6 <0) { x5=z5; change=1; }
		interMath::down();
		if (x1 + (-2)*z2 + x3 + x4 +(-2)*z5 + x6 >0) { z5=x5; change=1; }
		}
	}
	interMath::down();
	return  
	(x1*x4 +(- z3)*z4 + x1*x5 +(- 2)*z2*z5 + x3*x5 + x4*x5 
		+(- z5)*z5 +(- z1)*z6 + x3*x6 + x5*x6 >0);
	}

int PositiveDelta3(const double x[6],const double z[6])
	// return 1 if Delta3>0, 0 otherwise.
	{
	double xx[6]={x[0],x[2],x[1],x[3],x[5],x[4]};
	double zz[6]={z[0],z[2],z[1],z[3],z[5],z[4]};
	return PositiveDelta2(xx,zz);
	}

int PositiveDelta5(const double x[6],const double z[6])
	// return 1 if Delta5>0, 0 otherwise.
	{
	double xx[6]={x[0],x[4],x[5],x[3],x[1],x[2]}; 
	double zz[6]={z[0],z[4],z[5],z[3],z[1],z[2]};
	return PositiveDelta2(xx,zz);
	}

int PositiveDelta6(const double x[6],const double z[6])
	// return 1 if Delta5>0, 0 otherwise.
	{
	double xx[6]={x[0],x[5],x[4],x[3],x[2],x[1]}; 
	double zz[6]={z[0],z[5],z[4],z[3],z[2],z[1]};
	return PositiveDelta2(xx,zz);
	}

/*
int edgeBound::x4_upper_from_dih_upper
	(const double x[6],const double z[6],double theta,
	double& new_x4_upper)
	{
	// if we have an upper bound (theta) on the dihedral angle on a cell,
	// we can use that to compute an upper bound on the length of
	// the edge x4 (new_x4_upper).
	// This lemma relies on an embedded lemma, which was proved by hand, 
	// establishing the
	//  monotonicity of the dihedral angle in its edge lengths
	//  when y1,y4>=2.51, y2,y3,y5,y6 in [2,2.51].
	// or when y4>=sqrt8, y1>=2, and y2,y3,y5,y6 in [2,2.51].
	double x1=x[0], x2=z[1], x3=z[2], x4=x[3], x5=z[4], x6=z[5];
	if (((x1<6.3)&&(x4<8))
		||(x4<6.3)||
		(x1<4)||(x2<4)||(x3<4)||(x5<4)||(x6<4)||
		(x2>6.31)||(x3>6.31)||(x5>6.31)||(x6>6.31))
		{
		if ((!PositiveDelta2(x,z))||
			(!PositiveDelta3(x,z))||
			(!PositiveDelta5(x,z))||
			(!PositiveDelta6(x,z)))
			return 0;
		interMath::down();
		if (x[0]+x[1]-z[5] <0) return 0;
		if (x[0]+x[2]-z[4] <0) return 0;
		// at this point the edges along the vertex have arclength<pi/2
		// and delta2,delta3,delta5,delta6>0
		// monotonicity is justified.
		}
	// get rough guess with double, check later.
	// we are inverting for t: dih(x1,x2,x3,t,x5,x6)==theta;
	// denom of cosdih.
	double den = (x1*x1 - 2.0*x1*x3 + x3*x3 - 2.0*x1*x5 - 2.0*x3*x5 + x5*x5)
                *(x1*x1 - 2.0*x1*x2 + x2*x2 - 2.0*x1*x6 - 2.0*x2*x6 + x6*x6);
	if (den<0.0) { error::message("unexpected neg denom"); return 0; }
	double rhs = cos(theta)*sqrt(den);
	// D[delta,x4] = -2x1x4 + b:
	double b = -x1*x1 + x1*x2 + x1*x3 - x2*x3 + 
			x1*x5 + x2*x5 + x1*x6 + x3*x6 - x5*x6;
	if (x1<DBL_EPSILON) return 0;
	double trialx = (b-rhs)/(2.0*x1);
	double eps = 0.0001;
	trialx += eps; // We don't need a terribly good upper bound, but it
		// must be an upper bound.
	lineInterval dihx = linearization::dih(domain(x1,x2,x3,trialx,x5,x6));
	new_x4_upper=trialx;
	if (interMath::inf(dihx.f) > theta) return 1;
	return 0;
	}
*/

domain domain::lowerD(const interval tx[6])
    {
    double t[6];
    for (int i=0;i<6;i++) t[i]=interMath::inf(tx[i]);
    return domain(t[0],t[1],t[2],t[3],t[4],t[5]);
    }
 
domain domain::upperD(const interval tx[6])
    {
    double t[6];
    for (int i=0;i<6;i++) t[i]=interMath::sup(tx[i]);
    return domain(t[0],t[1],t[2],t[3],t[4],t[5]);
    }

/* testing routines */
static lineInterval setHyperInterval
	(double x0,double x1,double x2,double x3,double x4,double x5,double x6)
	{
	lineInterval a;
	a.f.hi=x0; a.Df[0].hi=x1; a.Df[1].hi=x2; a.Df[2].hi=x3; 
	a.Df[3].hi=x4; a.Df[4].hi=x5; a.Df[5].hi=x6;
	a.f.lo=x0; a.Df[0].lo=x1; a.Df[1].lo=x2; a.Df[2].lo=x3; 
	a.Df[3].lo=x4; a.Df[4].lo=x5; a.Df[5].lo=x6;
	return a;
	}

static int epsilonClose(lineInterval a,lineInterval b,double epsilon)
	{
	if (interMath::abs(a.f-b.f)>epsilon) return 0;
	for (int i=0;i<6;i++) if (interMath::abs(a.Df[i]-b.Df[i])>epsilon) return 0;
	return 1;
	}
	
	/////////
	// The tests in lineIntervalTest are not designed to catch
	// errors in rounding modes, or other errors that at the machine epsilon
	// level.  These are coarser tests designed to make sure we have
	// not left terms out of the polynomials, indexed a variable incorrectly
	// or some such thing.
void linearization::selfTest() {
	static const interval one("1");
	static int lineIntervalCount =0;
	if (interMath::sup(one)==0) return;
	if (lineIntervalCount++>0) return;
	cout << " -- loading lineInterval routines\n" << flush;
	//cout << one; return;
	assert(lineInterval(one).hi() == 1.0);
	domain x(4.04,4.08,4.12,4.16,4.2,4.24);

	/* (* Mathematica code for testing *)
      xD = {4.04, 4.08, 4.12, 4.16, 4.2, 4.24};

     testData[f_] := Module[{g, g0, g1, g2, g3,
       g4, g5, g6, xsub, x, x1, x2, x3, x4, x5, x6},
        g[x__] := f @@ Sqrt[{x}];
        xsub = {x1 -> xD[[1]], x2 -> xD[[2]], x3 -> xD[[3]], x4 -> xD[[4]], 
        x5 -> xD[[5]], x6 -> xD[[6]]};
        g0 = g @@ xD;
        g1 = D[g[x1, x2, x3, x4, x5, x6], x1] /. xsub;
        g2 = D[g[x1, x2, x3, x4, x5, x6], x2] /. xsub;
        g3 = D[g[x1, x2, x3, x4, x5, x6], x3] /. xsub;
        g4 = D[g[x1, x2, x3, x4, x5, x6], x4] /. xsub;
        g5 = D[g[x1, x2, x3, x4, x5, x6], x5] /. xsub;
        g6 = D[g[x1, x2, x3, x4, x5, x6], x6] /. xsub;
        N[{g0, g1, g2, g3, g4, g5, g6}, 30]//CForm];

       testData[Dihedral]
	 */

	/*test delta*/ {
	lineInterval MathematicaAnswer = setHyperInterval
		(141.772608,18.3056,17.6464,16.9616,17.2784,16.6384,15.9728);
	lineInterval ThisAnswer = linearization::delta(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-12))
		{
		cout << "delta failed = " << (MathematicaAnswer-ThisAnswer)
                << endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test dih*/ {
	lineInterval MathematicaAnswer = setHyperInterval
	  (1.224370849836081, 0.05570774552227705, -0.0562766050274816, 
		-0.05852660512963886, 0.1688085806309676, -0.05297589074342051, 
		-0.05520426522788236);
	lineInterval ThisAnswer = linearization::dih(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "dih failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test dih2*/ {
	lineInterval MathematicaAnswer = setHyperInterval
	  (1.237775343573561, -0.05655451587826826, 0.05708701867633032, 
    -0.06098974029484529, -0.05321742656790845, 0.169642208321201, 
    -0.05761081190165254);
	lineInterval ThisAnswer = linearization::dih2(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "dih2 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test dih3*/ {
	lineInterval MathematicaAnswer = setHyperInterval
	  (1.251642649880602, -0.05910323585352257, -0.06128798041222655, 
    0.05845294354919222, -0.05570611907234891, -0.05787069036015867, 
    0.1704717595191228);
	lineInterval ThisAnswer = linearization::dih3(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "dih3 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test dih4*/ {
	  lineInterval MathematicaAnswer = setHyperInterval 
   (1.2103723386199303,0.1712972934491306,
   -0.05373663326847471,-0.055975883938582466,
   0.05544797653750441,-0.0549098185072793,
							   -0.057126722791886006);
	lineInterval ThisAnswer = linearization::dih4(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "dih4 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test dih5*/ {
	  lineInterval MathematicaAnswer = setHyperInterval 
   (1.2238420530327385,-0.05401473258931138,
   0.1721188679153145,-0.058429840451965726,
   -0.05517317646186233,0.05683252430443883,
	  -0.05954497801152411);
	lineInterval ThisAnswer = linearization::dih5(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "dih5 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test dih6*/ {
	  lineInterval MathematicaAnswer = setHyperInterval (1.237773629512733,-0.05655420210343213,
   -0.058729572893063145,0.1729365393486911,
   -0.05767340245159547,-0.05982785360855054,
	  0.058206469608373966);
	lineInterval ThisAnswer = linearization::dih6(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "dih6 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test rhazim */ {
	  lineInterval MathematicaAnswer = setHyperInterval 
   (1.2284923443399745,0.15867695490603245,
   -0.05646604413275723,-0.05872361821714059,
   0.16937682646708305,-0.05315421893750245,
    -0.05539009460772968);
	lineInterval ThisAnswer = linearization::rhazim(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "rhazim failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test rhazim2 */ {
	  lineInterval MathematicaAnswer = setHyperInterval
    (1.2460880011116569,-0.05693432496492495,
   0.16086674754185729,-0.06139933548272868,
   -0.053574824414306485,0.1707814922705073,
     -0.057997714866165846);
	lineInterval ThisAnswer = linearization::rhazim2(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "rhazim2 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test rhazim3 */ {
	  lineInterval MathematicaAnswer = setHyperInterval 
   (1.2642204264321166,-0.059697165194383554,
   -0.06190386428530495,0.16308628826723298,
   -0.05626591073357978,-0.05845223383209246,
    0.17218483289496192); 
	lineInterval ThisAnswer = linearization::rhazim3(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "rhazim3 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test rhazim4 */ {
	  lineInterval MathematicaAnswer = setHyperInterval
   (1.2265502778924742,0.17358686759301012,
   -0.054454881663608706,-0.056724062347978284,
   0.15631945481589718,-0.05564374779575763,
							     -0.057890283410943405); 
	lineInterval ThisAnswer = linearization::rhazim4(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "rhazim4 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test rhazim5 */ {
	  lineInterval MathematicaAnswer = setHyperInterval 
  (1.244240127657498,-0.054915009339454826,
   0.17498761515550415,-0.05940370488398006,
   -0.05609276127917207,0.15854115872549165,
							     -0.06053742871380133); 
	lineInterval ThisAnswer = linearization::rhazim5(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "rhazim5 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test rhazim6 */ {
	  lineInterval MathematicaAnswer = setHyperInterval 
  (1.2624705818181052,-0.05768261233832029,
   -0.05990138769511693,0.17638709392693988,
   -0.05882414377914847,-0.061021582099667945,
   0.16079441566571734); 
	lineInterval ThisAnswer = linearization::rhazim6(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "rhazim6 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test solid*/ {
	lineInterval MathematicaAnswer = setHyperInterval
	  (0.5721961897004516, -0.05995000620951383, -0.06047756676337781, 
	-0.06106340187529186, 0.05988503499071025, 0.05879562721762187, 
		0.05765668238958797);
	lineInterval ThisAnswer = linearization::solid(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "solid failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test eta2_126*/ {
	lineInterval MathematicaAnswer = setHyperInterval
	  (1.373643196326929, 0.1089030755574367, 0.109889405933634, 0, 0, 0, 
    0.1144636780343532);
	lineInterval ThisAnswer = linearization::eta2_126(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "eta2_126 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test eta2_135*/ {
	lineInterval MathematicaAnswer = setHyperInterval
	  (1.373506019930212, 0.1089793717070623, 0, 0.111013297204093, 0, 
   0.1132987080363851, 0);
	lineInterval ThisAnswer = linearization::eta2_135(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "eta2_135 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test eta2_234*/ {
	lineInterval MathematicaAnswer = setHyperInterval
	 (  1.373376488703139, 0, 0.1100390734471457, 0.1110866694899548, 
   0.1121971131586948, 0, 0);
	lineInterval ThisAnswer = linearization::eta2_234(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "eta2_234 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test eta2_456*/ {
	lineInterval MathematicaAnswer = setHyperInterval
		 ( 1.400042333161984, 0, 0, 0, 0.1100593727913695, 0.1110875918750439, 
   0.112176286904411);
	lineInterval ThisAnswer = linearization::eta2_456(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "eta2_456 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test rad2*/ {
	lineInterval MathematicaAnswer = setHyperInterval
		  (1.55283590579077, 0.06062580892182253, 0.06059249803779962, 
    0.06055789352721254, 0.0643442214548576, 0.06437959485862623, 
    0.06441638319854542);
	lineInterval ThisAnswer = linearization::rad2(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "rad2 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}


	/*test delta_x4*/ {
	lineInterval MathematicaAnswer = setHyperInterval
		  (17.2784,0.2400000000000011,4.12,4.2,-8.08,3.880000000000001,
		   3.96);
	lineInterval ThisAnswer = linearization::delta_x4(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "delta_x4 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}


	/*test chi324*/ {
	lineInterval MathematicaAnswer = setHyperInterval
		  (71.98464, 16.8064, 0.5008, 
    -0.0032, 0.5008, 17.136, 16.9744);
	lineInterval ThisAnswer = linearization::chi324(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "chi324 failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		cout << "chi324 failed = " << (ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test x4_upper_from_dih_upper {
	double xx[6]={7.1,4.2,4.3,6.4,4.5,4.6};
	double outvalue;
	edgeBound::x4_upper_from_dih_upper(xx,xx,1.832330520094706,outvalue);
	outvalue -= 0.0001; // remove the epsilon...
	if (fabs(6.6 - outvalue)>1.0e-10)
		cout << "x4_upper failed = " << outvalue << "\n";
	}
	*/

	/*test edge_flat2_x */ {
	double outvalue =edge_flat2_x(4.1,4.2,4.3,4.5,4.6);
	if (fabs(13.47804480741523-outvalue)>1.0e-10)
		cout << "edge_flat2_x = " << outvalue << "\n";
	}

	/*test x4_upper_max*/
	// (Enclosed  @@ (Sqrt[{4.03, 4.05, 4.055, 4.0, 7.015, 7.01, 4.02, 4.06, 4.065}]))^2 
       {
	  double x4;
	  /* testA */ {
	  double xcd_lb = 4.0;
	  double xA[6]={4.0,4.0,4.0,4.0,4.0,4.0};
	  double xB[6]={4,4,4,4,4,4};
	  double x4 = edgeBound::x4_diag_max( xcd_lb,xA,xB,xA,xB);
	if (fabs(10.66666666666667 -x4)>1.0e-8)
		cout << "A: x4_upper_max = " << x4 << "\n"; 
	  }
	  /* testB */ {
	  double xcd_lb = 4.0;
	  double xA[6]={4.01,4.02,4.03,4.04,4.05,4.06};
	  double xB[6]={4.015,4.02,4.03,4.04,4.055,4.065};
	  double x4 = edgeBound::x4_diag_max( xcd_lb,xA,xB,xA,xB);
	if (fabs(10.841772254941086 -x4)>1.0e-8)
		cout << "B: x4_upper_max = " << x4 << "\n"; 
	  }
	  /* testC */ {
	  double xcd_lb = 4.0;
	  double xA[6]={7.01,4.02,4.03,4.04,4.05,4.06};
	  double xB[6]={7.015,4.02,4.03,4.04,4.055,4.065};
	  double x4 = edgeBound::x4_diag_max( xcd_lb,xA,xB,xA,xB);
	if (fabs(7.996812539196705 -x4)>1.0e-8)
		cout << "C: x4_upper_max = " << x4 << "\n"; 
	  }
	  /* testD flat case: EdgeFlat2X[4.0, 4.05, 4.06, 0,   4.065, 4.055] */ {
	  double xcd_lb = 4.0;
	  double xA[6]={4.01,4.02,4.03,4.04,4.05,4.06};
	  double xB[6]={4.015,4.02,4.03,4.04,4.055,4.065};
	  double zA[6]={4.01,7.02,7.03,4.04,4.05,4.06};
	  double zB[6]={4.015,7.02,7.03,4.04,4.055,4.065};
	  double x4 = edgeBound::x4_diag_max( xcd_lb,xA,xB,zA,zB);
	if (fabs(12.229985573375473 -x4)>1.0e-8)
		cout << "D: x4_upper_max = " << x4 << "\n"; 
	  }
	}

	/* test deltasup*/ {
	double t= deltasup(4.0,4.1,4.2,4.3,4.4,4.5);
	if ((fabs(152.604-t)>1.0e-10)||
		(t<152.604))
		{ cout << "deltasup failed = " << t << "\n"; }
		double u = ::delta(4.0,4.1,4.2,4.3,4.4,4.5);
	if ((fabs(u-t)>1.0e-12)|| (t<u))
		{ cout << "delta failed = " << t << "\n"; }
	}

	/* test dihedral*/ {
	double t = dihedralmin(4.0,4.1,4.2,4.3,4.4,4.5);
	if ((fabs(1.215755859685464005686485-t)>1.0e-9)||
		(t>1.215755859685464005686485))
		{ cout << "dihedralmin failed = " << t << "\n"; }
	double r = dihedralmin(8.575025,4,4.575025,8.575025,4,4.575025);
	if ((fabs(3.141592653589793238462643-r)>1.0e-4))
		{ cout << "dihedralmin2 failed = " << r << "\n"; }
	double u = dihedral(4.0,4.1,4.2,4.3,4.4,4.5);
	if ((fabs(u-t)>1.0e-9)||(u<t))
		{ cout << "dihedral failed = " << u << "\n"; }
	}

	/* test ExcessAngle*{
	double t = ExcessAngle(4.0,4.1,4.2,4.3,4.4,4.5,4.6,4.7,4.8);
	double u = ExcessAngleInf(4.0,4.1,4.2,4.3,4.4,4.5,4.6,4.7,4.8);
	if (t<u) 
		cout << "ExcessAngleInf failed = " << u << "\n";
	if (fabs(t-u)>1.0e-9)
		cout << "Excess failed = " << t << " " << u << "\n";
	if (fabs(t+2.7764844880256246130678471280)>1.0e-12)
		cout << "Excess failed(2) = " << t << "\n";
	}
	*/

	/* test x1supDELTA*/ {
	double u;
	double t = 8.2975893112399503863784921915;
	if (!x1supDELTA(4.0,4.1,4.2,4.3,u))
		cout << "x1supDELTA failed..." << endl;
	if ((fabs(u-t)>1.0e-6)||(u<t))
		cout << "x1supDELTA failed = " << u << endl;
	}

       /* test x3_upper_from_delta */ {
	 double deltaval = 0.14;
	 double x1 = 5.0; double x2 = 5.1;
         double x3 = 7.439246222317523;
	 double x3u = edgeBound::x3_upper_from_delta(deltaval,x1,x2);
	 if ((x3u < x3) || (fabs(x3 -x3u) > 1.0e-9)) {
	   cout << "x3_upper_from_delta fail " << x3 << " " << x3u << endl;
	 }
	 double x3l = edgeBound::x3_lower_from_delta(deltaval,x1,x2);
	 if ((x3 < x3l) || (fabs(x3-x3l) > 1.0e-9)) {
	   	   cout << "x3_lower_from_delta fail " << x3l << " " << x3 << endl;
	 }
       }

       /* test x4_upper_from_rad2 */ {
	 double x[6]={5.0,5.01,5.02,5.03,5.04,5.05};
	 double x4 = 6.585286666119991766;
	 double x4u = edgeBound::x4_upper_from_rad2(x);
	 if ((x4u < x4) || (fabs(x4 -x4u) > 1.0e-9)) {
	   cout << "x4_upper_from_rad2 fail " << x4 << " " << x4u << endl;
	 }
	 double x4l = edgeBound::x4_lower_from_rad2(x);
	 if ((x4 < x4l) || (fabs(x4-x4l) > 1.0e-9)) {
	   	   cout << "x4_lower_from_rad2 fail " << x4l << " " << x4 << endl;
	 }
       }

	/* test shortDiagMax {
	// test delta branch of procedure:
	double u=9.2973110504893041858; 
	double t=12.6;
	if (!edgeBound::shortDiagMax(4.1,4.2,4.3,4.4,6.3001,t,4.5,4.6,4.7,4.8))
		cout << "shortDiagMax failed..." << endl;
	if ((fabs(u-t)>1.0e-6)||(t<u))
		cout << "shortDiagMax failed = " << t << endl;
	// test exessAngle branch of procedure:
	u=9.1669539741566349590021602366;
	t=12.6;
	if (!edgeBound::shortDiagMax(5.1,5.2,4.3,4.4,6.3001,t,4.5,4.6,4.7,4.8))
		cout << "shortDiagMax failed..." << endl;
	if ((fabs(u-t)>1.0e-4)||(t<u))
		cout << "shortDiagMax failed = " << t << endl;
	}
	*/
	
	
	/* test chi234  {
	double u=85.1275;
	domain xx(4.1,4.2,4.3,4.4,4.5,4.6);
	domain z(4.15,4.25,4.35,4.45,4.55,4.65);
	double t = edgeBound::chi234min(xx,z);
	if ((fabs(u-t)>1.0e-12)||(t>u))
		cout << "chi234min failed = " << t << endl;
		}  
	*/



} 


