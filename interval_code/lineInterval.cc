//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

#include <iomanip.h>
#include <iostream.h>
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

/* (not used)
static lineInterval atan(lineInterval a)
	{
	static const interval one("1");
	return atan(a,one);
	}
*/

// modified arctan is defined as matan(x) = atan(sqrt(x))-sqrt(x)+sqrt(x)^3/3.
static void matan(const interval&u,const interval Du[2],
	interval& ma,interval Dma[2])
	{
	static const interval one("1");
	static const interval two("2");
	int i;
	interval t = interMath::sqrt(u);
	static const interval third= one/interval("3");
	// make use of monotonicity of matan in computation of its interval:
	interval atant = interMath::atan(t);
	double mau;
	interMath::up(); 
	mau = interMath::sup(atant) + (-interMath::sup(t)) 
	  + interMath::sup(t)*interMath::sup(u)*interMath::sup(third);
	//                 ^^ sup instead of inf by monotonicity.
	double man;
	interMath::down(); 
	man = interMath::inf(atant) + (-interMath::inf(t)) 
	  + interMath::inf(t)*interMath::inf(u)*interMath::inf(third);
	ma = interval(man,mau);
	interval x = t*u/(two*(one+u));
	for (i=0;i<2;i++) Dma[i]=Du[i]*x;
	}

static void compute_rogersterm(interval x,interval y,interval z,
	interval& f,interval Df[2])
	{ // Rogers5d:

	double  xn=interMath::inf(x), yyn=interMath::inf(y), zn=interMath::inf(z),
			xu=interMath::sup(x), yu=interMath::sup(y), zu=interMath::sup(z);
	interMath::up();
	double xu2=xu*xu, yu2=yu*yu, zu2=zu*zu;
	double xu3=xu*xu2, yu3=yu*yu2, zu3=zu*zu2;
	interMath::down();
	double xn2=xn*xn, yn2=yyn*yyn, zn2=zn*zn;
	double xn3=xn2*xn, yn3=yn2*yyn, zn3=zn2*zn;

	double fmin,fmax;
	interMath::down();
	fmin = //=Rogers5d
		2.0*xn2*xn*yn2 + 3.0*(xu*(yu2*(-yu2))) + 8.0*xn2*xn*yyn*zn
		+ 12.0*(xu*(yu2*(yu*(-zu)))) + 8.0*xn2*xn*zn2
		+ 12.0*(xu*(yu2*(-zu2))) +
		6.0*xn2*zn3 + 12.0*(xu*(yu*(-zu3))) + 8.0*yn2*zn3
		+ 3.0*(xu*(zu2*(-zu2))) + 8.0*yyn*zn2*zn2 +
		   2.0*zn2*zn2*zn;

	interMath::up();
	fmax = //=Rogers5d
		2.0*xu2*xu*yu2 + 3.0*(xn*(yn2*(-yn2))) + 8.0*xu2*xu*yu*zu
		+ 12.0*(xn*(yn2*(yyn*(-zn)))) + 8.0*xu2*xu*zu2
		+ 12.0*(xn*(yn2*(-zn2))) +
		6.0*xu2*zu3 + 12.0*(xn*(yyn*(-zn3))) + 8.0*yu2*zu3
		+ 3.0*(xn*(zn2*(-zn2))) + 8.0*yu*zu2*zu2 +
		   2.0*zu2*zu2*zu;
	f = interval(fmin,fmax);

	// Warning!! We never use the z-derivatives, so we set them to 0.

	// now for the first derivatives:
	double xmin[2],xmax[2];

	interMath::down();
	xmin[0]= 3.0*(2.0*xn2*yn2 +yu2*(-yu2)+8.0*xn2*yyn*zn+4.0*(yu3*(-zu))
		+8.0*xn2*zn2 + 4.0*(yu2*(-zu2))+4.0*xn*zn3 + 4.0*(yu*(-zu3))
		+zu2*(-zu2));
	xmin[1]= 4.0*(xn3*yyn + 3.0*(xu*(-yu3))+2.0*xn3*zn +9.0*(xu*(yu2*(-zu)))
		+6.0*(xu*(yu*(-zu2))) + 3.0*(xu*(-zu3))+4.0*yyn*zn3+2.0*zn2*zn2);

	interMath::up();
	xmax[0]= 3.0*(2.0*xu2*yu2 +yn2*(-yn2)+8.0*xu2*yu*zu +4.0*(yn3*(-zn))
		+8.0*xu2*zu2 + 4.0*(yn2*(-zn2))+4.0*xu*zu3 + 4.0*(yyn*(-zn3))
		+(zn2*(-zn2)));
	xmax[1]= 4.0*(xu3*yu + 3.0*(xn*(-yn3))+2.0*xu3*zu +9.0*(xn*(yn2*(-zn)))
		+6.0*(xn*(yyn*(-zn2))) + 3.0*(xn*(-zn3))+4.0*yu*zu3+2.0*zu2*zu2);
	for (int i=0;i<2;i++) Df[i]=interval(xmin[i],xmax[i]);
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

static void Dfivehalves(const interval& u,const interval Du[2],
	interval& fh,interval Dfh[2])
	{
	int i;
	interval sqrt_u = interMath::sqrt(u);
	static const interval two("2");
	static const interval fiveh = interval("5")/two;
	interval x = fiveh*u*sqrt_u;
	fh = sqrt_u*u*u;                        // Def' is u^(5/2) & derivs.
	for (i=0;i<2;i++) Dfh[i]= x*Du[i];
	}

static void compute_quoin(interval x,interval y,interval z,interval& f,
				interval Df[2] /* x and y derivatives */)
	// method two : tangent expansion.
	{
	static const interval zero("0");
	static const interval two("2");
	static const interval three("3");
	static const interval four("4");
	if ((interMath::sup(y)<interMath::inf(x))||
		(interMath::sup(z)<interMath::inf(y)))
		{
		f = Df[0]=Df[1]=zero; return;
		}
	int i;
	interval x2 = x*x;
	interval y2 = y*y;
	interval z2 = z*z;
	interval Df1[2];
	Df1[0]= three*(-x*x+z*z);
	Df1[1]= zero;
	interval f1 = (-x+z)*(x*x+x*z-two*z*z);

	interval unum = z2-y2;
	interval Dunum[2] = {zero,-two*y};
	interval uden = y2-x2;
	interval Duden[2]= {-two*x,two*y};

	interval u2, Du2[2];
	interval atu,Datu[2];
	quotient2(unum,Dunum,uden,Duden,u2,Du2);
	if (u2.lo<0.0) u2.lo=0.0;
	if (u2.hi<0.0) u2.hi=0.0;

	matan(u2,Du2,atu,Datu);
	interval g1,Dg1[2];
	product2(atu,Datu,f1,Df1,g1,Dg1);
	interval d5,Dd5[2];
	compute_rogersterm(x,y,z,d5,Dd5);
	interval fh,Dfh[2];
	Dfivehalves(u2,Du2,fh,Dfh);
	//interval lnum,Dlnum[2]; // same as uden //
	interval lden;
	interval yz = y+z; interval yz2=yz*yz; interval yz3=yz*yz2;
	lden = yz2*yz2*three;
	static const interval twelve("12");
	interval ldenf = twelve*yz3;
	interval Dlden[2] = {zero,ldenf};
	// interval ldenf2 = interval("36.0")*yz2; // not used.
	interval quo,Dquo[2];
	quotient2(uden,Duden,lden,Dlden,quo,Dquo);
	interval xx,Dxx[2];
	product2(quo,Dquo,fh,Dfh,xx,Dxx);
	interval g2,Dg2[2];
	product2(xx,Dxx,d5,Dd5,g2,Dg2);

	// Term g3.
	interval fz3 = four*z*z2;
	interval vnum = (-x+y)*(-y+z);
	interval Dvnum[2]= {y-z,-two*y+z+x};
	interval vden = (x+y)*(y+z);
	interval Dvden[2]= {y+z,two*y+z+x};
	interval v,Dv[2];
	quotient2(vnum,Dvnum,vden,Dvden,v,Dv);
	interval mv,Dmv[2];
	matan(v,Dv,mv,Dmv);
	interval g3,Dg3[2];
	g3 = mv*fz3;
	for (i=0;i<2;i++) Dg3[i]=fz3*Dmv[i];
	// Combine terms. m16 because we consistently left out a factor of -1/6.
	static const interval m16 = -interval("1")/interval("6");
	f = m16*(g1+g2+g3);
	for (i=0;i<2;i++) Df[i] = m16*(Dg1[i]+Dg2[i]+Dg3[i]);
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

static lineInterval chi126
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

lineInterval linearization::chi324(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	lineInterval t,s;
	s = chi126(x3,x2,x1,x6,x5,x4);
	int k[6]={2,1,0,5,4,3};
	for (int i=0;i<6;i++) t.Df[i]= s.Df[k[i]];
	t.f = s.f;
	return t;
	}


static lineInterval chi135
	(double x1,double x2,double x3,double x4,double x5,double x6)
	{
	lineInterval t,s;
	s = chi126(x1,x3,x2,x4,x6,x5);
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
	
//	deltaX := partial delta/partial x4.
lineInterval deltaX(double x1,double x2,double x3,double x4,double x5,double x6)
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
	lineInterval ax = -deltaX(x1,x2,x3,x4,x5,x6);
	double x14 = 4.0*x1;
	lineInterval t = lineInterval(interval(x14,x14));  
	t.Df[0]=four;
	lineInterval b2 = linearization::delta(x)*t;
	lineInterval b = sqrt(b2);
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

lineInterval linearization::gamma(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static const interval half("0.5");
	static const interval twothird("0.66666666666666666666666666666");
	static const interval mdoct6 = "-0.12015049158624418214";
	lineInterval t = sqrt(delta(x))*half;
	lineInterval a1,a2,a3,a4,b2,b3,b4;
	a1 = a(x1,x2,x3,x4,x5,x6);
	b2 = a(x1,x5,x6,x4,x2,x3);
	b3 = a(x4,x5,x3,x1,x2,x6);
	b4 = a(x4,x2,x6,x1,x5,x3);
	int i;
	{
	int k[6]= {0,4,5,3,1,2};
	a2.f = b2.f;
	for (i=0;i<6;i++) a2.Df[i]=b2.Df[k[i]];
	}
	{
	int k[6]= {3,4,2,0,1,5};
	a3.f = b3.f;
	for (i=0;i<6;i++) a3.Df[i]=b3.Df[k[i]];
	}
	{
	int k[6]= {3,1,5,0,4,2};
	a4.f = b4.f;
	for (i=0;i<6;i++) a4.Df[i]=b4.Df[k[i]];
	}
	return t*mdoct6+(atan(t,a1)+atan(t,a2)+atan(t,a3)+atan(t,a4))*twothird;
	}

lineInterval linearization::eta2(const domain& x)
	{	
	static const interval zero("0");
	double x1,x2,/*x3,x4,x5,*/x6;
	x1 = x.getValue(0); x2 = x.getValue(1); // x3 = x.getValue(2);
	// x4 = x.getValue(3); x5 = x.getValue(4); 
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
	lineInterval t = eta2(y);
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
	lineInterval t = eta2(y);
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
	lineInterval t = eta2(y);
	lineInterval u;
	u.f=t.f;
	static int k[6]={3,4,2,0,1,5};
	int i;
	for (i=0;i<6;i++) u.Df[i]=t.Df[k[i]];
	return u;
	}

static lineInterval quoin
	(double x1,double x2,double x6,interval trunc)
	{
	static const interval zero("0");
	static const interval eight("8");
	lineInterval et = sqrt(linearization::eta2(domain(x1,x2,0,0,0,x6)));
	interval a2,a0; a2 = interval(x1/4.0,x1/4.0); a0 = interMath::sqrt(a2);
	lineInterval s;
	interval Df[2];
	compute_quoin(a0,et.f,trunc,s.f,Df);
	s.Df[0]= Df[0]/(eight*a0) + Df[1]*et.Df[0];
	s.Df[1]= Df[1]*et.Df[1];
	s.Df[2]=s.Df[3]=s.Df[4]=zero;
	s.Df[5]= Df[1]*et.Df[5];
	return s;
	}

lineInterval linearization::quo(const domain& x) 
	{
	static const interval t0("1.255");
	return quoin(x.getValue(0),x.getValue(1),x.getValue(5),t0);
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

lineInterval linearization::vorAnalytic(const domain &x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static const interval mdoct4 = "-2.883611798069860371364";
	static const interval f43 = "1.333333333333333333333333333333";
	static const interval f48 = "48.0";
	lineInterval u126 = U126(x1,x2,x6), u135 = U135(x1,x3,x5),
	u234 = U324(x3,x2,x4);
	lineInterval vol = 
		f126(x1,x2,x3,x4,x6,x6)*chi126(x1,x2,x3,x4,x5,x6)/u126 +
		f324(x1,x2,x3,x4,x5,x6)*chi324(x)/u234 +
		f135(x1,x2,x3,x4,x5,x6)*chi135(x1, x2, x3, x4, x5, x6)/u135;
	vol = vol/(sqrt(delta(x))*f48);
	return vol*mdoct4 + solid(x)*f43;
	}

lineInterval linearization::VorInverted(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	int i;
	lineInterval s = vorAnalytic(domain(x1,x6,x5,x4,x3,x2));
	lineInterval t;
	t.f = s.f;
	int k[6]= {0,5,4,3,2,1}; // an involution.
	for (i=0;i<6;i++) t.Df[i]=s.Df[k[i]];
	return t;
	}

lineInterval linearization::rad2(const domain& x)
	{
	static const interval four("4");
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	lineInterval c = chi126(x1,x2,x3,x4,x5,x6);
	return c*c/(U126(x1,x2,x6)*delta(x)*four) 
			+ eta2(domain(x1,x2,0,0,0,x6));
	}

lineInterval linearization::chi126squaredOverEtc(const domain& x)
	{
	static const interval four("4");
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	lineInterval c = chi126(x1,x2,x3,x4,x5,x6);
	return c*c/(U126(x1,x2,x6)*delta(x)*four) ;
	}

	//////////
	//
	// Bdih = (A(y1/2)+phi0) dih(S).
	// 
static lineInterval Bdih(const domain& x,
	interval trunc,int long_edge_allowed=0)
	{
	static const interval zero("0");
	static const interval two("2");
	static const interval three("3");
	static const interval four("4");
	static const interval mdoct_12 = "-0.0600752457931220910701037362515";
	static const interval doct_8 = -mdoct_12*three/two;
	static const interval f_3 ("1.333333333333333333333333333333");
	static const interval mdoc_43 = "-0.96120393268995345712165978002";
	interval trunc2 = trunc*trunc;
	lineInterval d = linearization::dih(x);
	// phi0dih = phi[trunc,trunc] dih.
	lineInterval phi0dih = d*(f_3 + mdoc_43*trunc2*trunc);

	double x1 = x.getValue(0); 
	interval xx(x1,x1);
	interval sqrtx = interMath::sqrt(xx);
	interval r = (-two*trunc+sqrtx); 
	if (interMath::sup(r)>1.0e-10) 
		{
		if (long_edge_allowed) return phi0dih;
		error::message("inappropriate use of Bdih");
		cout << "sqrtx= " << sqrtx << endl << flush; 
		}
	r = -interMath::pos(-r);
	lineInterval A; A.f = -mdoct_12*r*r*(four*trunc+sqrtx);
	for (int i=0;i<6;i++) A.Df[i]=zero;
	A.Df[0]= -doct_8*interMath::pos(four*trunc2-xx)/sqrtx;
	return A*d+phi0dih;  // By SPIV. B[y] = A[y/2]+phi0.
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

static lineInterval quoins
	(double x1,double x2,double x3,double x4,double x5,double x6,
	interval trunc)
	{
	lineInterval 	q12 = quoin(x1,x2,x6,trunc),
		q13 = quoin(x1,x3,x5,trunc),
		q21 = quoin(x2,x1,x6,trunc),
		q23 = quoin(x2,x3,x4,trunc),
		q31 = quoin(x3,x1,x5,trunc),
		q32 = quoin(x3,x2,x4,trunc);
	lineInterval r12,r13,r21,r23,r31,r32;
	r12=q12;
	r13=permute(q13,0,2,1,3,5,4);
	r21=permute(q21,1,0,2,4,3,5);
	r23=permute(q23,2,0,1,5,3,4);
	r31=permute(q31,1,2,0,4,5,3);
	r32=permute(q32,2,1,0,5,4,3);
	return r12+r13+r21+r23+r31+r32;
	}

static lineInterval quoins234
	(double,double x2,double x3,double x4,double,double,
	interval trunc)
	{
	lineInterval 	q23 = quoin(x2,x3,x4,trunc),
		q32 = quoin(x3,x2,x4,trunc);
	lineInterval r23,r32;
	r23=permute(q23,2,0,1,5,3,4);
	r32=permute(q32,2,1,0,5,4,3);
	return r23+r32;
	}

static lineInterval vorVc
	(double x1,double x2,double x3,double x4,double x5,double x6,
	interval trunc)
	{
	double cut = 4*interMath::sup(trunc*trunc);
	if ((x1>cut)|| (x2>cut)|| (x3>cut))
		error::message("bad argument supplied to vorVc");
	static const interval three("3");
	static const interval f_3 ("1.333333333333333333333333333333");
	static const interval mdoc_43 = "-0.96120393268995345712165978002";
	static const interval pi = "3.14159265358979323846264338328";
	static const interval doct4 = -mdoc_43*three;
	interval consterm = (f_3 + mdoc_43*trunc*trunc*trunc)*pi;
	lineInterval d1 = Bdih(domain(x1,x2,x3,x4,x5,x6),trunc);
	lineInterval d2 = Bdih(domain(x2,x1,x3,x5,x4,x6),trunc);
	lineInterval d3 = Bdih(domain(x3,x2,x1,x6,x5,x4),trunc);
	interval t; // swap into correct order:
	t=d2.Df[0]; d2.Df[0]=d2.Df[1]; d2.Df[1]=t;
	t=d2.Df[3]; d2.Df[3]=d2.Df[4]; d2.Df[4]=t;
	t=d3.Df[0]; d3.Df[0]=d3.Df[2]; d3.Df[2]=t;
	t=d3.Df[3]; d3.Df[3]=d3.Df[5]; d3.Df[5]=t;
	return d1+d2+d3-quoins(x1,x2,x3,x4,x5,x6,trunc)*doct4-consterm;
	}

static lineInterval uprightvorVc
	(double x1,double x2,double x3,double x4,double x5,double x6,
	interval trunc)
	{
	static const interval three("3");
	static const interval four("4");
	interval cut = four*trunc*trunc;
	if ((x2>interMath::sup(cut))||
		(x3>interMath::sup(cut))||
		(x1<interMath::inf(cut)))
		error::message("bad argument supplied to uprightvorVc");
	static const interval f_3 ("1.333333333333333333333333333333");
	static const interval mdoc_43 = "-0.96120393268995345712165978002";
	static const interval pi = "3.14159265358979323846264338328";
	static const interval doct4 = -mdoc_43*three;
	interval consterm = (f_3 + mdoc_43*trunc*trunc*trunc)*pi;
	lineInterval d1 = Bdih(domain(x1,x2,x3,x4,x5,x6),trunc,1);
	lineInterval d2 = Bdih(domain(x2,x1,x3,x5,x4,x6),trunc);
	lineInterval d3 = Bdih(domain(x3,x2,x1,x6,x5,x4),trunc);
	interval t; // swap into correct order:
	t=d2.Df[0]; d2.Df[0]=d2.Df[1]; d2.Df[1]=t;
	t=d2.Df[3]; d2.Df[3]=d2.Df[4]; d2.Df[4]=t;
	t=d3.Df[0]; d3.Df[0]=d3.Df[2]; d3.Df[2]=t;
	t=d3.Df[3]; d3.Df[3]=d3.Df[5]; d3.Df[5]=t;
	return d1+d2+d3-quoins234(x1,x2,x3,x4,x5,x6,trunc)*doct4-consterm;
	}

lineInterval linearization::VorVc(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static const interval t("1.255");
	return vorVc(x1,x2,x3,x4,x5,x6,t);
	}

lineInterval linearization::Vor1385(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static const interval t("1.385");
	return vorVc(x1,x2,x3,x4,x5,x6,t);
	}

lineInterval linearization::uprightVorVc(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static const interval t("1.255");
	return uprightvorVc(x1,x2,x3,x4,x5,x6,t);
	}

lineInterval linearization::uprightVorVcInverted(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	int i;
	lineInterval s = uprightVorVc(domain(x1,x6,x5,x4,x3,x2));
	lineInterval t;
	t.f = s.f;
	int k[6]= {0,5,4,3,2,1};
	for (i=0;i<6;i++) t.Df[i]=s.Df[k[i]];
	return t;
	}

lineInterval linearization::VorSqc(const domain& x)
	{
	double x1,x2,x3,x4,x5,x6;
	x1 = x.getValue(0); x2 = x.getValue(1); x3 = x.getValue(2);
	x4 = x.getValue(3); x5 = x.getValue(4); x6 = x.getValue(5);
	static const interval t("1.41421356237309504880168872421");
	return vorVc(x1,x2,x3,x4,x5,x6,t);
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
static double dihedralinf
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


// Assuming opposite edges to x3 on 3 simplices have lengths at least
// x0min,x3min,x0pmin, calculate the Excess angle over 2pi.
// If one of the terms is "greater than pi" (geometrically speaking),
// then the geometric excess will be even greater than the return
// value.
static double ExcessAngle
	(double x0min,double x0pmin,double x1,double x2,double x3min,
	double x4,double x4p,double x5,double x5p)
	{
	static const double pi2=6.28318530717958647692528676656;
	return dihedral(x3min,x4,x2,x0min,x1,x5)+
	  dihedral(x3min,x4,x4p,x3min,x5p,x5)+
	  dihedral(x3min,x4p,x2,x0pmin,x1,x5p)-pi2;
	}

// Same as ExcessAngle but use careful intervals rather than 
// floating point.
static double ExcessAngleInf
	(double x0min,double x0pmin,double x1,double x2,double x3min,
	double x4,double x4p,double x5,double x5p)
	{
	static const interval pi2("6.28318530717958647692528676656");
	double d1=dihedralinf(x3min,x4,x2,x0min,x1,x5),
	  d2= dihedralinf(x3min,x4,x4p,x3min,x5p,x5),
	  d3 = dihedralinf(x3min,x4p,x2,x0pmin,x1,x5p);
	interMath::down();
	return d1+d2+d3-interMath::sup(pi2);
	}


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

	/*test gamma*/ {
	lineInterval MathematicaAnswer = setHyperInterval
	  (0.01975528077233823, -0.04566103833985133, -0.04506689836142777, 
    -0.04447779293358099, -0.04193097824527764, -0.04138040496415922, 
    -0.04083396666833738);
	lineInterval ThisAnswer = linearization::gamma(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "gamma failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test eta2*/ {
	lineInterval MathematicaAnswer = setHyperInterval
	  (1.373643196326929, 0.1089030755574367, 0.109889405933634, 0, 0, 0, 
    0.1144636780343532);
	lineInterval ThisAnswer = linearization::eta2(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "eta2 failed = " << (MathematicaAnswer-ThisAnswer)
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

	/*test chi126squaredOverEtc*/ {
	lineInterval MathematicaAnswer = setHyperInterval
		( 0.1791927094638431, -0.04827726663561425, -0.04929690789583435, 
		0.06055789352721258, 0.06434422145485768, 0.06437959485862619, 
		-0.05004729483580777);
	lineInterval ThisAnswer = linearization::chi126squaredOverEtc(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "rad2 failed = " << (MathematicaAnswer-ThisAnswer)
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

	/*test vorAnalytic */ {
	lineInterval MathematicaAnswer = setHyperInterval
		  (0.02975516833884084, -0.07571540919858652, -0.07420774316145259, 
    -0.07271212399542648, -0.01481484335869471, -0.01519798350605676, 
    -0.01558173388510887);
	lineInterval ThisAnswer = linearization::vorAnalytic(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-9))
		{
		cout << "vorAnalytic failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test VorVc */ {
	// use new domain so that Rad>1.255;
	domain z(4.14,4.08,4.12,4.16,4.2,4.24);
	lineInterval MathematicaAnswer = setHyperInterval
		  (0.02239727638322316, -0.07138317679892827, -0.07451602566673953, 
    -0.07300643854813292, -0.01592304492280537, -0.01540175383741551, 
    -0.01577197942928313);
	lineInterval ThisAnswer = linearization::VorVc(z);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-8))
		{
		cout << "VorVc failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		cout << "VorVc failed = " << ThisAnswer
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test VorSqc */ {
	// use new domain so that Rad>sqrt(2);
	domain z(4.94,4.98,4.92,7,4.8,4.84);
	lineInterval MathematicaAnswer = setHyperInterval
		( -0.2597616779487081, -0.07288587250300103, -0.05214710431438422, 
    -0.0545770739349982, -0.03171574795244974, -0.05310067279640517, 
    -0.0526962997262784);
	lineInterval ThisAnswer = linearization::VorSqc(z);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-8))
		{
		cout << "VorSqc failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		cout << "VorSqc failed = " << ThisAnswer
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test Vor1385 */ {
	// use new domain so that Rad>1.385;
	domain z(4.94,4.98,4.92,7,4.8,4.84);
	lineInterval MathematicaAnswer = setHyperInterval
	 (-0.2594625272052193, -0.07254153705301419, -0.05139469025525832, 
   -0.05383162002685866, -0.03053430820810097, -0.05258279881458921, 
   -0.05217343132181529);
	lineInterval ThisAnswer = linearization::Vor1385(z);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-8))
		{
		cout << "VorSqc failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		cout << "VorSqc failed = " << ThisAnswer
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test VorInverted */ {
	lineInterval MathematicaAnswer = setHyperInterval
		  (0.01664456784635159, -0.07611735548795519, -0.01575286229548984, 
    -0.01608336935298273, -0.01423143983855594, -0.06786394366567112, 
    -0.06640100863645138);
	lineInterval ThisAnswer = linearization::VorInverted(x);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-8))
		{
		cout << "VorInverted failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		cout << "VorInverted failed = " << ThisAnswer
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test uprightVorVc */ {
	// use new domain so that y1>2.51;
	domain z(7,4.98,4.92,4,4.8,4.84);
	lineInterval MathematicaAnswer = setHyperInterval
		  (-0.1514990866278141, 0.0169484693935585, -0.04596710543235722, 
    -0.04953540952028351, -0.02751799025996786, -0.01773336458764444, 
    -0.01680364768904157);
	lineInterval ThisAnswer = linearization::uprightVorVc(z);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-8))
		{
		cout << "uprightVorVc failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		cout << "uprightVorVc failed = " << ThisAnswer
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test uprightVorVcInverted */ {
	// use new domain so that y1>2.51;
	domain z(7,4.98,4.92,4,4.8,4.84);
	lineInterval MathematicaAnswer = setHyperInterval
		(-0.1428970603500303, 0.01741080759166868, -0.01663159449795801, 
    -0.01755642156853108, -0.02852521188212975, -0.05434462871151318, 
    -0.05149311417970992);
	lineInterval ThisAnswer = linearization::uprightVorVcInverted(z);
	if (!epsilonClose(MathematicaAnswer,ThisAnswer,1.0e-8))
		{
		cout << "uprightVorVcInverted failed = " << (MathematicaAnswer-ThisAnswer)
				<< endl << flush;
		cout << "uprightVorVcInverted failed = " << ThisAnswer
				<< endl << flush;
		error::message("lineInterval failed to install properly");
		}
	}

	/*test x4_upper_from_dih_upper*/ {
	double xx[6]={7.1,4.2,4.3,6.4,4.5,4.6};
	double outvalue;
	edgeBound::x4_upper_from_dih_upper(xx,xx,1.832330520094706,outvalue);
	outvalue -= 0.0001; // remove the epsilon...
	if (fabs(6.6-outvalue)>1.0e-10)
		cout << "x4_upper failed = " << outvalue << "\n";
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
	double t = dihedralinf(4.0,4.1,4.2,4.3,4.4,4.5);
	if ((fabs(1.215755859685464005686485-t)>1.0e-9)||
		(t>1.215755859685464005686485))
		{ cout << "dihedralinf failed = " << t << "\n"; }
	double r = dihedralinf(8.575025,4,4.575025,8.575025,4,4.575025);
	if ((fabs(3.141592653589793238462643-r)>1.0e-4))
		{ cout << "dihedralinf2 failed = " << r << "\n"; }
	double u = dihedral(4.0,4.1,4.2,4.3,4.4,4.5);
	if ((fabs(u-t)>1.0e-9)||(u<t))
		{ cout << "dihedral failed = " << u << "\n"; }
	}

	/* test ExcessAngle*/{
	double t = ExcessAngle(4.0,4.1,4.2,4.3,4.4,4.5,4.6,4.7,4.8);
	double u = ExcessAngleInf(4.0,4.1,4.2,4.3,4.4,4.5,4.6,4.7,4.8);
	if (t<u) 
		cout << "ExcessAngleInf failed = " << u << "\n";
	if (fabs(t-u)>1.0e-9)
		cout << "Excess failed = " << t << " " << u << "\n";
	if (fabs(t+2.7764844880256246130678471280)>1.0e-12)
		cout << "Excess failed(2) = " << t << "\n";
	}

	/* test x1supDELTA*/ {
	double u;
	double t = 8.2975893112399503863784921915;
	if (!x1supDELTA(4.0,4.1,4.2,4.3,u))
		cout << "x1supDELTA failed..." << endl;
	if ((fabs(u-t)>1.0e-6)||(u<t))
		cout << "x1supDELTA failed = " << u << endl;
	}

	/* test shortDiagMax*/ {
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
	
	/* test chi234 */ {
	double u=85.1275;
	domain xx(4.1,4.2,4.3,4.4,4.5,4.6);
	domain z(4.15,4.25,4.35,4.45,4.55,4.65);
	double t = edgeBound::chi234min(xx,z);
	if ((fabs(u-t)>1.0e-12)||(t>u))
		cout << "chi234min failed = " << t << endl;
	}

	/* test quoin */ {
	double q = 0.00091536560156357352747615;
	double qq[6]={-0.001175131924613549419,-0.00159469529124843039,
			0,0,0,-0.0016354898219547855};
	interval trunc ("1.255");
	lineInterval s = quoin(4.1,4.2,4.3,trunc);
	if ((s.low()>q)||(s.hi()<q)||(fabs(s.low()-q)>1.0e-9)||
			(fabs(s.hi()-q)>1.0e-9))
		cout << "quoin = " << s.low() <<" " << s.hi() << endl;
	for (int i=0;i<6;i++) if
		((interMath::inf(s.partial(i))>qq[i])||
		 (interMath::sup(s.partial(i))<qq[i])||
		 (interMath::sup(s.partial(i))-
			interMath::inf(s.partial(i))>1.0e-10))
		cout << "quoin partial" << i << " " << s.partial(i) << endl;
	}



} 


