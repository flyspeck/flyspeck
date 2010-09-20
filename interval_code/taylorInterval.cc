/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                            */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                     */
/* ========================================================================== */

// parameter passing modes (const-reference parameters)
// http://pages.cs.wisc.edu/~hasti/cs368/CppTutorial/NOTES/PARAMS.html


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
#include "interval.h"
#include "univariate.h"
#include "lineInterval.h"
#include "secondDerive.h"
#include "taylorInterval.h"

using namespace std;
using namespace tr1;


static inline double max(double x,double y)
{ return (x>y ? x : y); }

static inline double dabs(const interval x) {
  return interMath::sup(interMath::max(x,-x));
}

static void intervalToAbsDouble(const interval DDx[6][6],double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) 	
			  DD[i][j]= dabs(DDx[i][j]);
}

static lineInterval plus (const lineInterval& f, const lineInterval& g)  {
  lineInterval h;
  h.f = f.f + g.f;
  for (int i=0;i<6;i++) {
    h.Df[i] = f.Df[i] + g.Df[i];
  }
  return h;
}

/* ========================================================================== */
/*                                                                            */
/*   primitiveA                                                               */
/*                                                                            */
/* ========================================================================== */


class primitiveA : public primitive 
{
private:
  lineInterval (*hfn)(const domain&);
  
  // all the arrays of double [6][6] are bounds on abs value of second partials.
  int (*setAbsSecond)(const domain& x,const domain& z,double [6][6]);
  
public:
  lineInterval tangentAt(const domain& x) const { return (*hfn)(x); }
  taylorInterval evalf4(const domain& w,const domain& x,
			const domain& y,const domain& z) const;
  primitiveA(lineInterval (*)(const domain& ),
	     int (*)(const domain& ,const domain&,double [6][6]));
};


taylorInterval primitiveA::evalf4
(const domain& w,const domain& x,const domain& y,const domain& z) const
{
  double DD[6][6];
  (*setAbsSecond)(x,z,DD);
  lineInterval tangentVector = (*hfn)(y);
  return taylorInterval(tangentVector,w,DD);
}

primitiveA::primitiveA(lineInterval (*hfn0)(const domain&),
		       int (*setAbsSecond0)(const domain&,const domain&,double [6][6]))
{
  hfn = hfn0;
  setAbsSecond = setAbsSecond0;
}


/* ========================================================================== */
/*                                                                            */
/*   primitive_univariate                                                     */
/*                                                                            */
/* ========================================================================== */


class primitive_univariate : public primitive 
{
private:
  int slot;
  const univariate* f;
  
public:
  
  lineInterval tangentAt(const domain& x) const ;
  
  taylorInterval evalf4(const domain& w,const domain& x,
			const domain& y,const domain& z) const;
  
  primitive_univariate(const univariate&x, int slot0 ) { f = &x; slot = slot0; };
};

lineInterval primitive_univariate::tangentAt(const domain& x) const {
  static interval zero("0");
  lineInterval a;
  double y = x.getValue(slot);
  interval t(y,y);
  a.f = f->eval(t,0);
  for (int i=1;i<6;i++) a.Df[i]=zero;
  a.Df[slot] = f->eval(t,1);
  return a;
}

taylorInterval primitive_univariate::evalf4(const domain& w,const domain& x,
					    const domain& y,const domain& z) const {
  double DD[6][6];
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) { DD[i][j]=0.0; }
  interval t(x.getValue(slot),z.getValue(slot));
  DD[slot][slot] = dabs(f->eval(t,2));
  taylorInterval a(primitive_univariate::tangentAt(y),w,DD);
  return a;
}

/* ========================================================================== */
/*                                                                            */
/*   primitiveC  composites                                                   */
/*                                                                            */
/* ========================================================================== */


class primitiveC : public primitive 
{
private:
  const taylorFunction* hdr;
  const taylorFunction* p1;
  const taylorFunction* p2;
  const taylorFunction* p3;
  const taylorFunction* p4;
  const taylorFunction* p5;
  const taylorFunction* p6;
  
public:
  
  lineInterval tangentAt(const domain& x) const ;
  
  taylorInterval evalf4(const domain& w,const domain& x,
			const domain& y,const domain& z) const;
  
  primitiveC(const taylorFunction* ,
	     const taylorFunction*,const taylorFunction*,const taylorFunction*,
	     const taylorFunction*,const taylorFunction*,const taylorFunction*
	     );
};

primitiveC::primitiveC
  (const taylorFunction* hdr0, 
   const taylorFunction* p10,const taylorFunction* p20,const taylorFunction* p30,
   const taylorFunction* p40,const taylorFunction* p50,const taylorFunction* p60) 
{
  hdr = hdr0;
  p1 = p10;
  p2  =p20;
  p3 = p30;
  p4 = p40;
  p5 = p50;
  p6 = p60;
};

lineInterval primitiveC::tangentAt(const domain& x) const
{
  if (!hdr) { error::fatal ("tangentAt: function expected, returning 0");   }
  lineInterval pv[6];
  pv[0] = p1->tangentAt(x);
  pv[1] = p2->tangentAt(x);
  pv[2] = p3->tangentAt(x);
  pv[3] = p4->tangentAt(x);
  pv[4] = p5->tangentAt(x);
  pv[5] = p6->tangentAt(x);
  // calculate narrow value range of pv[i].
  double a[6], b[6];
  for (int i=0;i<6;i++) {
    a[i]=interMath::inf(pv[i].f); b[i] =interMath::sup(pv[i].f);
  }
  domain aN(a);
  domain bN(b);
  // 
  // value of outer function
  taylorInterval fN = hdr->evalf(aN,bN);
  // derivatives of outer function
  interval fN_partial[6]; // narrow partials (at interval image of a point)
  interval pN_partial[6][6];  // function i, partial j.
  for (int i=0;i<6;i++) {
    interval tN(fN.lowerPartial(i),fN.upperPartial(i));
    fN_partial[i] = tN;
    for (int j=0;j<6;j++) {
      pN_partial[i][j] = pv[i].Df[j];
    }
  }
  // apply chain rule to compute narrow first derivative data.
  interval cN_partial[6];
  static interval zero("0");
  for (int i=0;i<6;i++) {
    cN_partial[i] = zero;
    for (int j=0;j<6;j++) { cN_partial[i]  =cN_partial[i] + fN_partial[j] * pN_partial[j][i]; }
  }
  lineInterval lin;
  lin.f = fN.tangentVectorOf().f;
  for (int i=0;i<6;i++) {
    lin.Df[i] = cN_partial[i];
  }
  return lin;
};

taylorInterval primitiveC::evalf4(const domain& w,const domain& x,const domain& y,const domain& z ) const
{
  if (!hdr) { error::fatal ("evalf4: function expected, returning 0");   }
  
  taylorInterval pv[6] = {
    p1->evalf4(w,x,y,z),
    p2->evalf4(w,x,y,z),
    p3->evalf4(w,x,y,z),
    p4->evalf4(w,x,y,z),
    p5->evalf4(w,x,y,z),
    p6->evalf4(w,x,y,z)};
  
  // calculate wide value range of pv[i], 
  double a[6], b[6];
  for (int i =0;i<6;i++) {
    a[i] = pv[i].lowerBound(); b[i] = pv[i].upperBound(); 
  }
  domain aW(a);
  domain bW(b);
  // calculate narrow value range of pv[i].
  for (int i=0;i<6;i++) {
    a[i]=pv[i].tangentVectorOf().low(); b[i] =pv[i].tangentVectorOf().hi();
  }
  domain aN(a);
  domain bN(b);
  
  // value of outer function
  taylorInterval fW = hdr->evalf(aW,bW);
  taylorInterval fN = hdr->evalf(aN,bN);
  // derivatives of outer function
  interval fW_partial[6]; // wide partials (over entire domain)
  interval fN_partial[6]; // narrow partials (at interval image of a point)
  interval pW_partial[6][6]; // function i, partial j.
  interval pN_partial[6][6];  
  for (int i=0;i<6;i++) {
    interval tW(fW.lowerPartial(i),fW.upperPartial(i));
    fW_partial[i] = tW;
    interval tN(fN.lowerPartial(i),fN.upperPartial(i));
    fN_partial[i] = tN;
    for (int j=0;j<6;j++) {
      interval uW(pv[i].lowerPartial(j),pv[i].upperPartial(j));
      pW_partial[i][j] = uW;
      pN_partial[i][j] = pv[i].tangentVectorOf().partial(j);
    }
  }
  // apply chain rule to compute narrow first derivative data.
  interval cN_partial[6];
  static interval zero("0");
  for (int i=0;i<6;i++) {
    cN_partial[i] = zero;
    for (int j=0;j<6;j++) { cN_partial[i]  =cN_partial[i] + fN_partial[j] * pN_partial[j][i]; }
  }
  // apply chain rule to compute bound on second derivative data. 
  // This is the "wide" part of the calc.
  double DcW[6][6];
  interMath::up();
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      DcW[i][j]= 0.0;
      for (int k=0;k<6;k++) {
	DcW[i][j] = DcW[i][j] + dabs(fW_partial[k]) * pv[k].DD[i][j];
	for (int m=0;m<6;m++) {
	  DcW[i][j] = DcW[i][j] + fW.DD[k][m] * dabs(pW_partial[k][i]) * dabs(pW_partial[m][j]);
	}
      }
    }
  lineInterval lin;
  lin.f = fN.tangentVectorOf().f;
  for (int i=0;i<6;i++) {
    lin.Df[i] = cN_partial[i];
  }
  taylorInterval ch(lin,w,DcW);
  return ch;
};


/* ========================================================================== */
/*                                                                            */
/*   taylorSimplex                                                            */
/*                                                                            */
/* ========================================================================== */




static void testAbs(double DD[6][6],char* s) {
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      if (DD[i][j] < 0) {
	error::message("negative absolute value detected " );
	cout << s << " " << DD[i][j] << " " << i << " " << j << endl;
      }
    }
}

/*implement unit*/
static int setZero(const domain& ,const domain& ,double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
  testAbs(DD,"setZero");
  return 1;
}
static lineInterval unit(const domain& )
{
  static const interval one("1");
  return lineInterval(one);
}
static primitiveA scalr(unit,setZero);
const taylorFunction taylorSimplex::unit(&scalr);

/*implement x1 */
static lineInterval lineX1(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(0),x.getValue(0)));
  h.Df[0]=one;
  return h;
}
primitiveA x1(lineX1,setZero);
const taylorFunction taylorSimplex::x1(&::x1);

/*implement x2 */
static lineInterval lineX2(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(1),x.getValue(1)));
  h.Df[1]=one;
  return h;
}
primitiveA x2(lineX2,setZero);
const taylorFunction taylorSimplex::x2(&::x2);

/*implement x3 */
static lineInterval lineX3(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(2),x.getValue(2)));
  h.Df[2]=one;
  return h;
}
primitiveA x3(lineX3,setZero);
const taylorFunction taylorSimplex::x3(&::x3);

/*implement x4 */
static lineInterval lineX4(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(3),x.getValue(3)));
  h.Df[3]=one;
  return h;
}
primitiveA x4(lineX4,setZero);
const taylorFunction taylorSimplex::x4(&::x4);

/*implement x5 */
static lineInterval lineX5(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(4),x.getValue(4)));
  h.Df[4]=one;
  return h;
}
primitiveA x5(lineX5,setZero);
const taylorFunction taylorSimplex::x5(&::x5);

/*implement x6 */
static lineInterval lineX6(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(5),x.getValue(5)));
  h.Df[5]=one;
  return h;
}
primitiveA x6(lineX6,setZero);
const taylorFunction taylorSimplex::x6(&::x6);

/*implement y1 */
static lineInterval sqrt(lineInterval a)
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
  return sqrt(h);
}

static int setY1(const domain& x,const domain&,double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
  double x0 = x.getValue(0);
  if (x0<1.0e-8) return 0;
  interMath::down();
  double y = sqrt(x0);
  double y3 = 4.0*y*y*y;
  interMath::up();
  if (y3</*float.h*/DBL_EPSILON) return 0;
  DD[0][0]= 1.0/y3;
  testAbs(DD,"setY1");
  return 1;
}
primitiveA Y1(lineY1,setY1);
const taylorFunction taylorSimplex::y1(&::Y1);

/*implement y2 */
static lineInterval lineY2(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(1),x.getValue(1)));
  h.Df[1]=one;
  return sqrt(h);
}
static int setY2(const domain& x,const domain&,double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
  double x0 = x.getValue(1);
  if (x0<1.0e-8) return 0;
  interMath::down();
  double y = sqrt(x0);
  double y3 = 4.0*y*y*y;
  if (y3</*float.h*/DBL_EPSILON) return 0;
  interMath::up();
  DD[1][1]= 1.0/y3;
  testAbs(DD,"setY2");
  return 1;
}
primitiveA Y2(lineY2,setY2);
const taylorFunction taylorSimplex::y2(&::Y2);

/*implement y3 */
static lineInterval lineY3(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(2),x.getValue(2)));
  h.Df[2]=one;
  return sqrt(h);
}
static int setY3(const domain& x,const domain&,double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
  double x0 = x.getValue(2);
  if (x0<1.0e-8) return 0;
  interMath::down();
  double y = sqrt(x0);
  double y3 = 4.0*y*y*y;
  if (y3</*float.h*/DBL_EPSILON) return 0;
  interMath::up();
  DD[2][2]= 1.0/y3;
  testAbs(DD,"setY3");
  return 1;
}
primitiveA Y3(lineY3,setY3);
const taylorFunction taylorSimplex::y3(&::Y3);

/*implement y4 */
static lineInterval lineY4(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(3),x.getValue(3)));
  h.Df[3]=one;
  return sqrt(h);
}
static int setY4(const domain& x,const domain&,double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
  double x0 = x.getValue(3);
  if (x0<1.0e-8) return 0;
  interMath::down();
  double y = sqrt(x0);
  double y3 = 4.0*y*y*y;
  if (y3</*float.h*/DBL_EPSILON) return 0;
  interMath::up();
  DD[3][3]= 1.0/y3;
  testAbs(DD,"setY4");
  return 1;
}
primitiveA Y4(lineY4,setY4);
const taylorFunction taylorSimplex::y4(&::Y4);

/*implement y5 */
static lineInterval lineY5(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(4),x.getValue(4)));
  h.Df[4]=one;
  return sqrt(h);
}
static int setY5(const domain& x,const domain&,double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
  double x0 = x.getValue(4);
  if (x0<1.0e-8) return 0;
  interMath::down();
  double y = sqrt(x0);
  double y3 = 4.0*y*y*y;
  if (y3</*float.h*/DBL_EPSILON) return 0;
  interMath::up();
  DD[4][4]= 1.0/y3;
  testAbs(DD,"setY5");
  return 1;
}
primitiveA Y5(lineY5,setY5);
const taylorFunction taylorSimplex::y5(&::Y5);

/*implement y6 */
static lineInterval lineY6(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(5),x.getValue(5)));
  h.Df[5]=one;
  return sqrt(h);
}
static int setY6(const domain& x,const domain&,double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
  double x0 = x.getValue(5);
  if (x0<1.0e-8) return 0;
  interMath::down();
  double y = sqrt(x0);
  double y3 = 4.0*y*y*y;
  if (y3</*float.h*/DBL_EPSILON) return 0;
  interMath::up();
  DD[5][5]= 1.0/y3;
  testAbs(DD,"setY6");
  return 1;
}
primitiveA Y6(lineY6,setY6);
const taylorFunction taylorSimplex::y6(&::Y6);

/*implement x1*x2 */
static lineInterval lineX1X2(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(0),x.getValue(0)) * 
		 interval(x.getValue(1),x.getValue(1)));
  h.Df[0]=one;
  h.Df[1]=one;
  return h;
}
static int setX1X2DD(const domain& ,const domain& ,double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
  DD[1][0]=1.0;
  DD[0][1]=1.0;
  testAbs(DD,"setX1X2DD");
  return 1;
}
static primitiveA x1x2Prim(lineX1X2,setX1X2DD);
static const taylorFunction x1x2(&::x1x2Prim);


/*implement delta */
static int setAbsDelta(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  interval DDh[6][6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  secondDerive::setDelta(X,Z,DDh);
  intervalToAbsDouble(DDh,DD);
  testAbs(DD,"setAbsDelta");
  return 1;
}
primitiveA deltaPrimitive(linearization::delta,setAbsDelta);
const taylorFunction taylorSimplex::delta(&::deltaPrimitive);

/*implement vol_x */ 
static interval one("1");
static interval twelve("12");
static taylorFunction f_twelth = taylorSimplex::y1 * (one/ twelve);
primitiveC volXPrimitive
 (&f_twelth,
  &taylorSimplex::delta  , &taylorSimplex::unit, &taylorSimplex::unit,
  &taylorSimplex::unit  , &taylorSimplex::unit, &taylorSimplex::unit);
const taylorFunction taylorSimplex::vol_x(&::volXPrimitive);

/*implement dih1*/
static int setAbsDihedral(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  int r = secondDerive::setAbsDihedral(X,Z,DD);
  if (r) { testAbs(DD,"setAbsDihedral"); }
  return r;
}
primitiveA dih1Primitive(linearization::dih,setAbsDihedral);
const taylorFunction taylorSimplex::dih(&::dih1Primitive);

/*implement dih2*/
static int setAbsDih2(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  interval s,Ds[6],DDs[6][6];
  int outcome = secondDerive::setSqrtDelta(X,Z,s,Ds,DDs);
  if (!outcome) return outcome;
  interval h,Dh[6],DDh[6][6];
  outcome = secondDerive::setDih2(X,Z,s,Ds,DDs,h,Dh,DDh);
  if (!outcome) return outcome;
  intervalToAbsDouble(DDh,DD);
  testAbs(DD,"setAbsDih2");
  return outcome;
}
primitiveA dih2Primitive(linearization::dih2,setAbsDih2);
const taylorFunction taylorSimplex::dih2(&::dih2Primitive);

/*implement dih3*/
static int setDih3(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  interval s,Ds[6],DDs[6][6];
  int outcome = secondDerive::setSqrtDelta(X,Z,s,Ds,DDs);
  if (!outcome) return outcome;
  interval h,Dh[6],DDh[6][6];
  outcome = secondDerive::setDih3(X,Z,s,Ds,DDs,h,Dh,DDh);
  if (!outcome) return outcome;
  intervalToAbsDouble(DDh,DD);
  return outcome;
}
primitiveA dih3Primitive(linearization::dih3,setDih3);
const taylorFunction taylorSimplex::dih3(&::dih3Primitive);

/*implement dih4 : |- dih4_y y1 y2 y3 y4 y5 y6 = dih_y y4 y2 y6 y1 y5 y3 */ 
primitiveC dih4Primitive
(&taylorSimplex::dih,
  &taylorSimplex::x4  , &taylorSimplex::x2, &taylorSimplex::x6,
  &taylorSimplex::x1 , &taylorSimplex::x5, &taylorSimplex::x3);
const taylorFunction taylorSimplex::dih4(&::dih4Primitive);

/*implement dih5 : |- dih5_y y1 y2 y3 y4 y5 y6 = dih_y y5 y1 y6 y2 y4 y3 */
primitiveC dih5Primitive
(&taylorSimplex::dih,
  &taylorSimplex::x5  , &taylorSimplex::x1, &taylorSimplex::x6,
  &taylorSimplex::x2 , &taylorSimplex::x4, &taylorSimplex::x3);
const taylorFunction taylorSimplex::dih5(&::dih5Primitive);

/*implement dih6 : |- dih6_y y1 y2 y3 y4 y5 y6 = dih_y y6 y1 y5 y3 y4 y2 */
primitiveC dih6Primitive
(&taylorSimplex::dih,
  &taylorSimplex::x6  , &taylorSimplex::x1, &taylorSimplex::x5,
  &taylorSimplex::x3 , &taylorSimplex::x4, &taylorSimplex::x2);
const taylorFunction taylorSimplex::dih6(&::dih6Primitive);


/*implement azim*/
static int setRhazim(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  interval s,Ds[6],DDs[6][6];
  int outcome = secondDerive::setSqrtDelta(X,Z,s,Ds,DDs);
  if (!outcome) return outcome;
  interval h,Dh[6],DDh[6][6];
  outcome = secondDerive::setDihedral(X,Z,s,Ds,DDs,h,Dh,DDh);
  if (!outcome) return outcome;
  interval DDa[6][6];
  outcome = secondDerive::setRhazim(X[0],Z[0],h,Dh,DDh,DDa);
  intervalToAbsDouble(DDa,DD);
  return outcome;
}
primitiveA rhazimPrimitive(linearization::rhazim,setRhazim);
const taylorFunction taylorSimplex::rhazim(&::rhazimPrimitive);

/*implement azim2*/
static int setRhazim2(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  interval s,Ds[6],DDs[6][6];
  int outcome = secondDerive::setSqrtDelta(X,Z,s,Ds,DDs);
  if (!outcome) return outcome;
  interval h,Dh[6],DDh[6][6];
  outcome = secondDerive::setDih2(X,Z,s,Ds,DDs,h,Dh,DDh);
  if (!outcome) return outcome;
  interval DDa[6][6];
  outcome = secondDerive::setRhazim2(X[1],Z[1],h,Dh,DDh,DDa);
  intervalToAbsDouble(DDa,DD);
  return outcome;
}
primitiveA rhazim2Primitive(linearization::rhazim2,setRhazim2);
const taylorFunction taylorSimplex::rhazim2(&::rhazim2Primitive);

/*implement azim3*/
static int setRhazim3(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  interval s,Ds[6],DDs[6][6];
  int outcome = secondDerive::setSqrtDelta(X,Z,s,Ds,DDs);
  if (!outcome) return outcome;
  interval h,Dh[6],DDh[6][6];
  outcome = secondDerive::setDih3(X,Z,s,Ds,DDs,h,Dh,DDh);
  if (!outcome) return outcome;
  interval DDa[6][6];
  outcome = secondDerive::setRhazim3(X[2],Z[2],h,Dh,DDh,DDa);
  intervalToAbsDouble(DDa,DD);
  return outcome;
}
primitiveA rhazim3Primitive(linearization::rhazim3,setRhazim3);
const taylorFunction taylorSimplex::rhazim3(&::rhazim3Primitive);

/*implement sol*/
static int setSol(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  int i,j;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  interval s,Ds[6],DDs[6][6],DDx[6][6];
  if (!(secondDerive::setSqrtDelta(X,Z,s,Ds,DDs))) return 0;
  if (!(secondDerive::setSolid(X,Z,s,Ds,DDs,DDx))) return 0;
  for (i=0;i<6;i++) for (j=i;j<6;j++)
		      DD[i][j]=dabs(DDx[i][j]);
  for (i=0;i<6;i++) for (j=0;j<i;j++) DD[i][j]=DD[j][i];
  return 1;
}
primitiveA solPrimitive(linearization::solid,setSol);
const taylorFunction taylorSimplex::sol(&::solPrimitive);

static int copy(double DD[6][6],const double sec[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++)
			  DD[i][j]=sec[i][j];
  return 1;
}

/* implement gchi (univariate) */ 
// gchi (sqrt x) = &4 * mm1 / pi -(&504 * mm2 / pi)/ &13 +(&200 * (sqrt x) * mm2 /pi)/ &13
static interval i_gchi_c0("0.974990367692870754241952463595");
static interval i_gchi_c1("0.124456752559607807811255454313");
static univariate i_gchi = univariate::i_sqrt * i_gchi_c1 + univariate::i_pow0 * i_gchi_c0;
/*implement gchi1_x x1 x2 x3 x4 x5 x6 = gchi (sqrt x1) * dih_x x1 x2 x3 x4 x5 x6; */
/*
static primitive_univariate i_gchi1P(&::i_gchi, 0 );
static primitive_univariate i_gchi2P(&::i_gchi, 1 );
static primitive_univariate i_gchi3P(&::i_gchi, 2 );
static primitive_univariate i_gchi4P(&::i_gchi, 3 );
static primitive_univariate i_gchi5P(&::i_gchi, 4 );
static primitive_univariate i_gchi6P(&::i_gchi, 5 );
static taylorFunction i_gchi1(&::i_gchi1P);
static taylorFunction i_gchi2(&::i_gchi2P);
static taylorFunction i_gchi3(&::i_gchi3P);
static taylorFunction i_gchi4(&::i_gchi4P);
static taylorFunction i_gchi5(&::i_gchi5P);
static taylorFunction i_gchi6(&::i_gchi6P);

static primitiveC gchi1XPrim
(&::x1x2,
  &::i_gchi1  , &taylorSimplex::dih, &taylorSimplex::unit,
  &taylorSimplex::unit , &taylorSimplex::unit, &taylorSimplex::unit);
const taylorFunction taylorSimplex::gchi1_x(&::gchi1XPrim);
*/

/*implement eta2_126*/
static int setEta2_126(const domain& x,const domain& z,double DD[6][6])
{
  // use bounds from SECOUT/out.eta2
  static const int k[3]={0,1,5};
  x.getValue(0); // useless line
  z.getValue(0); // useless line
  int i,j;
  for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=0.0;
  for (i=0;i<3;i++) for (j=0;j<3;j++) DD[k[i]][k[j]]=0.09;
  return 1;
}
primitiveA eta2Primitive(linearization::eta2,setEta2_126);
const taylorFunction taylorSimplex::eta2_126(&::eta2Primitive);

/*implement eta2_135*/
static int setEta2_135(const domain& x,const domain& z,double DD[6][6])
{
  // use bounds from SECOUT/out.eta2
  static const int k[3]={0,2,4};
  x.getValue(0); // useless line
  z.getValue(0); // useless line
  int i,j;
  for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=0.0;
  for (i=0;i<3;i++) for (j=0;j<3;j++) DD[k[i]][k[j]]=0.09;
  return 1;
}
primitiveA eta2_135_Primitive(linearization::eta2_135,setEta2_135);
const taylorFunction taylorSimplex::eta2_135(&::eta2_135_Primitive);

/*implement eta2_234*/
static int setEta2_234(const domain& x,const domain& z,double DD[6][6])
{
  // use bounds from SECOUT/out.eta2
  static const int k[3]={1,2,3};
  x.getValue(0); // useless line
  z.getValue(0); // useless line
  int i,j;
  for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=0.0;
  for (i=0;i<3;i++) for (j=0;j<3;j++) DD[k[i]][k[j]]=0.09;
  return 1;
}
primitiveA eta2_234_Primitive(linearization::eta2_234,setEta2_234);
const taylorFunction taylorSimplex::eta2_234(&::eta2_234_Primitive);

/*implement eta2_456*/
static int setEta2_456(const domain& x,const domain& z,double DD[6][6])
{
  // use bounds from SECOUT/out.eta2
  static const int k[3]={3,4,5};
  x.getValue(0); // useless line
  z.getValue(0); // useless line
  int i,j;
  for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=0.0;
  for (i=0;i<3;i++) for (j=0;j<3;j++) DD[k[i]][k[j]]=0.09;
  return 1;
}
primitiveA Peta2_456(linearization::eta2_456,setEta2_456);
const taylorFunction taylorSimplex::eta2_456(&::Peta2_456);

static int primHasDeltaDenom(const primitive* p) {
  return
    ((p == &dih1Primitive) || (p == &dih2Primitive) || (p == &dih3Primitive) ||
     (p == &rhazimPrimitive) || (p== &rhazim2Primitive) || (p == &rhazim3Primitive) ||
     (p == &solPrimitive));
}

/* ========================================================================== */
/*                                                                            */
/*   taylorInterval                                                           */
/*                                                                            */
/* ========================================================================== */




taylorInterval::taylorInterval(domain w0) {
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) { DD[i][j]=0.0; }
  w = w0;
}

taylorInterval::taylorInterval(const lineInterval& h0,
			       const domain& w0,const double DD0[6][6])
{
  w = w0;
  for (int i=0;i<6;i++) {
    if (w.getValue(i) < 0.0) { error::message("constructing neg width ");
      cout << w.getValue(i) << " " << (w0.getValue(i)-w.getValue(i)) << " " << i << endl;
    }
  }
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      if (DD0[i][j] < 0.0) { error::message("invalid DD input"); 
	cout << i << " " << j << " " << DD0[i][j] << endl;
      }
    }
  tangentVector = h0;
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=DD0[i][j];
}

lineInterval taylorInterval::tangentVectorOf() const
{
  return tangentVector;
}

static double taylorError(const domain& w,const double DD[6][6])
{
  interMath::up();
  double t=0.0;
  int i,j;
  for (i=0;i<6;i++) {
    if (w.getValue(i) < 0.0) { 
      error::message("negative width"); cout << w.getValue(i); }
  }
  for (i=0;i<6;i++) for (j=0;j<6;j++) {
      if (DD[i][j] < 0.0)  { error::message("negative abs in taylorError"); } 
    }
  for (i=0;i<6;i++) t = t + (w.getValue(i)*w.getValue(i))*DD[i][i];
  t = t/2.0;
  for (i=0;i<6;i++) for (j=i+1;j<6;j++)
		      t = t+ (w.getValue(i)*w.getValue(j))*DD[i][j];
  return t;
}

double taylorInterval::upperBound() const {
  double err = taylorError(w,DD);
  interMath::up();
  double t = tangentVector.hi() + err;
  for (int i=0;i<6;i++) t = t+ w.getValue(i)*dabs(tangentVector.partial(i));
  return t;
}

double taylorInterval::lowerBound() const {
  double err = taylorError(w,DD);
  interMath::down();
  double t = tangentVector.low() - err;
  for (int i=0;i<6;i++) t = t + (-w.getValue(i))*dabs(tangentVector.partial(i));
  return t;
}

double taylorInterval::upperboundQ 
(const taylorInterval& cA,const taylorInterval& cB) {
  interMath::up();
  double err = taylorError(cA.w,cA.DD)+taylorError(cB.w,cB.DD);
  double t = cA.tangentVector.hi()+cB.tangentVector.hi() + err;
  int k[3]={0,4,5},i;
  for (i=0;i<3;i++) t = 
		      t+ cA.w.getValue(k[i])*dabs(cA.tangentVectorOf().partial(k[i]));
  for (i=0;i<3;i++) t = 
		      t+ cB.w.getValue(k[i])*dabs(cB.tangentVectorOf().partial(k[i]));
  for (i=1;i<4;i++) t = t+ cB.w.getValue(i)*
		      dabs(cB.tangentVectorOf().partial(i)+cA.tangentVectorOf().partial(i));
  return t;
}

double taylorInterval::lowerboundQ
(const taylorInterval& cA,const taylorInterval& cB)
{
  interMath::up();
  double err = taylorError(cA.w,cA.DD)+taylorError(cB.w,cB.DD);
  interMath::down();
  double t = cA.tangentVector.low()+cB.tangentVector.low() - err;
  int k[3]={0,4,5},i;
  for (i=0;i<3;i++) t = t+ 
		      (-cA.w.getValue(k[i]))*dabs(cA.tangentVectorOf().partial(k[i]));
  for (i=0;i<3;i++) t = t+ 
		      (-cB.w.getValue(k[i]))*dabs(cB.tangentVectorOf().partial(k[i]));
  for (i=1;i<4;i++) t = t+ (-cB.w.getValue(i))
		      *dabs(cB.tangentVectorOf().partial(i)+cA.tangentVectorOf().partial(i));
  return t;
}


double taylorInterval::upperPartial(int i) const
{
  if ((i<0)||(i>=6)) 
    { error::message("upperPartial index out of range"); return 0; }
  interMath::up();
  double err = 0.0;
  for (int j=0;j<6;j++) err  = err + w.getValue(j)*DD[i][j];
  return interMath::sup(tangentVector.partial(i)) + err;
}

double taylorInterval::lowerPartial(int i) const
{
  if ((i<0)||(i>=6)) 
    { error::message("upperPartial index out of range"); return 0; }
  interMath::up();
  double err = 0.0;
  for (int j=0;j<6;j++) err  = err + w.getValue(j)*DD[i][j];
  interMath::down();
  return interMath::inf(tangentVector.partial(i)) - err;
}

taylorInterval taylorInterval::plus
(const taylorInterval& t1,const taylorInterval& t2)
{
  double DD[6][6];
  int i,j;
  interMath::up();
  for (i=0;i<6;i++) for (j=0;j<6;j++) 
		      DD[i][j]= t1.DD[i][j]+t2.DD[i][j];
  lineInterval s;
  s.f = t1.tangentVector.f + t2.tangentVector.f;
  for (i=0;i<6;i++) s.Df[i]= t1.tangentVector.Df[i]+ t2.tangentVector.Df[i];
  for (i=0;i<6;i++) if (t1.w.getValue(i)!=t2.w.getValue(i)) 
		      error::message("bad domain in ti");
  taylorInterval t(s,t1.w,DD);
  return t;
}

taylorInterval taylorInterval::scale
(const taylorInterval& t1,const interval& c)
{
  double absC = dabs(c); // interMath::sup(interMath::max(c,-c));
  double DD[6][6];
  interMath::up();
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) 
			  { DD[i][j]= t1.DD[i][j]*absC; }
  lineInterval s = t1.tangentVector;
  s.f = s.f *c;
  for (int i=0;i<6;i++) s.Df[i]=s.Df[i]*c;
  taylorInterval t(s,t1.w,DD);
  return t;
}

/* ========================================================================== */
/*                                                                            */
/*   taylorFunction                                                           */
/*                                                                            */
/* ========================================================================== */



taylorFunction::taylorFunction(const taylorFunction& rhs)
{
  for (mapPrim::const_iterator it = rhs.data.begin(); it!= rhs.data.end(); ++it)
    data[it->first]=it->second;
}

// constructor from a primitive.
taylorFunction::taylorFunction(void* p) {
  static interval one("1");
  data[p] = one;
}

taylorFunction& taylorFunction::operator=(const taylorFunction& ) 
{
  error::message("assignment not implemented");
  return *this;
}

taylorFunction::~taylorFunction()
{
}

taylorFunction taylorFunction::operator*(const interval& x) const  {
  taylorFunction a(*this);
  for (mapPrim::const_iterator ia = a.data.begin();ia!=a.data.end();++ia) {
    a.data[ia->first] = ia->second * x;
  }
  return a;
}

taylorFunction taylorFunction::operator+(const taylorFunction& rhs) const {
  taylorFunction lhs(*this);
  mapPrim::iterator ilhs = lhs.data.begin();
  for (mapPrim::const_iterator irhs = rhs.data.begin();
       irhs!=rhs.data.end();++irhs) {
    ilhs = lhs.data.find(irhs->first);
    if (ilhs != lhs.data.end()) {      
      lhs.data[irhs->first] = ilhs->second + irhs->second;    
    }
    else {      lhs.data[irhs->first] = irhs->second;    }
  }
  return lhs;
}

taylorInterval taylorFunction::evalf4(const domain& w, const domain& x,const domain& y, const domain& z) const {
  taylorInterval t(w);
  for (mapPrim::const_iterator ia = this->data.begin();
      ia!=this->data.end();++ia) {
    t = taylorInterval::plus(t,
      taylorInterval::scale((*((primitive*)(ia->first))).evalf4(w,x,y,z),
				       ia->second));
  }
  return t;
};

taylorInterval taylorFunction::evalf
(const domain& x,const domain& z) const
{
  double w[6],y[6];
  int i;
  interMath::nearest();
  for (i=0;i<6;i++) y[i]=(z.getValue(i)+x.getValue(i))/2.0;
  interMath::up();
  for (i=0;i<6;i++) {
    w[i]=max(z.getValue(i)-y[i],
	     y[i]-x.getValue(i));
    assert(w[i] >= 0.0);
  }
  domain wD(w[0],w[1],w[2],w[3],w[4],w[5]);
  domain yD(y[0],y[1],y[2],y[3],y[4],y[5]);
  
  return taylorFunction::evalf4(wD,x,yD,z);
}

lineInterval taylorFunction::tangentAt(const domain& x) const {
  lineInterval t;
  lineInterval temp;
  for (mapPrim::const_iterator ia = this->data.begin();ia!=this->data.end();++ia) {
    temp =  ((primitive*)(ia->first))->tangentAt(x);
    t.f = t.f + temp.f * ia -> second;
    for (int i=0;i<6;i++) { t.Df[i] = t.Df[i] + temp.Df[i] * ia->second; }
  }
  return t;
};


void taylorFunction::setReducibleState(int i)
{ reduState = i; }

int taylorFunction::getReducibleState() const
{ return reduState; }


int taylorFunction::hasDeltaDenom() const {
  taylorFunction u  (*this);
  for (mapPrim::const_iterator it = u.data.begin(); it!= u.data.end(); ++it) {
    primitive* p = (primitive*) (it->first);
    if (primHasDeltaDenom(p)) { return 1; } }
  return 0;
}


/* ========================================================================== */
/*                                                                            */
/*    TESTING ROUTINES                                                        */
/*                                                                            */
/* ========================================================================== */


static int epsilonClose(double x,interval y,double epsilon)
{
  if (interMath::abs(y-interval(x,x))>epsilon)
    {
      cout << "close : " << interMath::abs(y-interval(x,x))
	   << " " << x << " " << y << endl<< flush;
      return 0;
    }
  return 1;
}

static int epsilonCloseDoubles(double x,double y,double epsilon)
{
  if (abs(y-x)>epsilon)
    {
      cout << "close-doubles : " << abs(y-x)
	   << " " << x << " " << y << endl<< flush;
      return 0;
    }
  return 1;
}


static int barelyLess(double x,double y,double epsilon)
{
  if ((x>y)||(y>x+epsilon))
    {
      cout << "barelyLess " << x << " " << y << endl << flush;
      return 0;
    }
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

static double rand(int i,const domain& x,const domain& z,double t=1)
{
  return x.getValue(i) + t*rand01()*(z.getValue(i)-x.getValue(i));
}

static domain makeDomain(int i,const domain& x,const domain& z)
{
  int a[6]; int b=1;
  int j;
  for (j=0;j<6;j++)
    {
      a[j]= (i/b) % 2; // binary conversion
      b= b*2;
    }
  return domain(
		x.getValue(0)+ a[0]*(z.getValue(0)-x.getValue(0)),
		x.getValue(1)+ a[1]*(z.getValue(1)-x.getValue(1)),
		x.getValue(2)+ a[2]*(z.getValue(2)-x.getValue(2)),
		x.getValue(3)+ a[3]*(z.getValue(3)-x.getValue(3)),
		x.getValue(4)+ a[4]*(z.getValue(4)-x.getValue(4)),
		x.getValue(5)+ a[5]*(z.getValue(5)-x.getValue(5)));
}

//////////
//
// This compares the corners with the taylor upper bound.
// If the taylor upper bound is not close to the corner upper bound
// or if the taylor upper bound is less than a corner value, and
// error is issued.  There can be false reporting of errors here
// because the computed corner value might be much larger than
// the actual corner value (because of atan approximations, etc. ).
// Or the taylor upper bound might be extremely conservative and
// give an upper bound that is much bigger than needs be.

static void testProcedure(taylorFunction F,lineInterval (*G)(const domain&),
			  const domain& x,const domain& z,char* s,double epsilon=1.0e-9)
{
  double t = 1.0e-5; 
  domain xx(rand(0,x,z),rand(1,x,z),rand(2,x,z),
	    rand(3,x,z),rand(4,x,z),rand(5,x,z));
  domain zz(rand(0,xx,z,t),rand(1,xx,z,t),rand(2,xx,z,t),
	    rand(3,xx,z,t),rand(4,xx,z,t),rand(5,xx,z,t));
  taylorInterval f = F.evalf(xx,zz); // evaluate f at random small cell.
  
  /*get max*/{
    int i,j;
    double temp = -/*float.h*/DBL_MAX; 
    double Dtemp[6]; for (i=0;i<6;i++) Dtemp[i]= -DBL_MAX;
    for (i=0;i<64;i++) 
      {
	domain c = makeDomain(i,xx,zz); 
	lineInterval li = (*G)(c);
	if (temp<li.hi()) temp = li.hi();
	for (j=0;j<6;j++) if (Dtemp[j]<interMath::sup(li.partial(j)))
			    Dtemp[j]=interMath::sup(li.partial(j));
      }
    for (int k=0;k<6;k++) 
      if (!barelyLess(Dtemp[k],f.upperPartial(k),epsilon))
	{
	  cout << "testProc Dmax("<<k<<") failed " << s << endl;
	  cout << "found = " << Dtemp[k] << " bounded by = " << 
	    f.upperPartial(k) << endl;
	  interMath::up();
	  cout << "diff = " << f.upperPartial(k) - Dtemp[k] << endl;
	  for (j=0;j<6;j++) cout << xx.getValue(j) << " "; cout << endl;
	  for (j=0;j<6;j++) cout << zz.getValue(j) << " "; cout << endl;
	}
    if (!barelyLess(temp,f.upperBound(),epsilon))
      {
	cout << "\n\ntestProc max failed " << s << endl;
	cout << "found = " << temp << " bounded by = " << f.upperBound() << endl;
	cout << "diff = " << f.upperBound() - temp << endl;
	for (j=0;j<6;j++) cout << xx.getValue(j) << " "; cout << endl;
	for (j=0;j<6;j++) cout << zz.getValue(j) << " "; cout << endl;
	cout << "tangentVector = " << f.tangentVector.hi() << endl;
	cout << "widths = "; for (j=0;j<6;j++) cout << f.w.getValue(j)<<" " << endl;
	cout << "center partials= "; 
	for (j=0;j<6;j++) cout << f.tangentVector.partial(j) << " " << endl;
	cout << "taylorError " << taylorError(f.w,f.DD) << endl << endl;
      }
    
  }
  
  /*get min*/{
    int i,j;
    double temp = /*float.h*/DBL_MAX; 
    double Dtemp[6]; for (i=0;i<6;i++) Dtemp[i]= DBL_MAX;
    for (i=0;i<64;i++) 
      {
	domain c = makeDomain(i,xx,zz); 
	lineInterval li = (*G)(c);
	if (temp>li.low()) temp = li.low();
	for (j=0;j<6;j++) if (Dtemp[j]>interMath::inf(li.partial(j)))
			    Dtemp[j]=interMath::inf(li.partial(j));
      }
    for (int k=0;k<6;k++) 
      if (!barelyLess(f.lowerPartial(k),Dtemp[k],epsilon))
	{
	  cout << "testProc Dmin("<<k<<") failed " << s << endl;
	  cout << "found = " << Dtemp[k] << " bounded by = " << 
	    f.lowerPartial(k) << endl;
	  interMath::up();
	  cout << "diff = " << -f.lowerPartial(k) + Dtemp[k] << endl;
	  for (j=0;j<6;j++) cout << xx.getValue(j) << " "; cout << endl;
	  for (j=0;j<6;j++) cout << zz.getValue(j) << " "; cout << endl;
	}
    if (!barelyLess(f.lowerBound(),temp,epsilon))
      {
	cout << "testProc min failed " << s << endl;
	cout << "found = " << temp << " bounded by = " << f.lowerBound() << endl;
	cout << "diff = " << f.lowerBound() - temp << endl;
	for (j=0;j<6;j++) cout << xx.getValue(j) << " "; cout << endl;
	for (j=0;j<6;j++) cout << zz.getValue(j) << " "; cout << endl;
      }
  }  
}

void taylorFunction::selfTest()
{
  cout << " -- loading taylor routines " << endl;
  /*test Proc*/{
    testProcedure(taylorSimplex::x1,lineX1,domain(2,2,2,2,2,2),
		  domain(2.51,2.51,2.51,2.51,2.51,2.51),"x1");
    testProcedure(taylorSimplex::dih,linearization::dih,
		  domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		  "taylorSimplex::dih");
    testProcedure(taylorSimplex::dih2,linearization::dih2,
		  domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		  "taylorSimplex::dih2");
    testProcedure(taylorSimplex::dih3,linearization::dih3,
		  domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		  "taylorSimplex::dih3");
    testProcedure(taylorSimplex::sol,linearization::solid,
		  domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		  "taylorSimplex::sol");
    testProcedure(taylorSimplex::eta2_126,linearization::eta2,
		  domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		  "taylorSimplex::eta2_126",5.0e-6);
    testProcedure(taylorSimplex::eta2_135,linearization::eta2_135,
		  domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		  "taylorSimplex::eta2_135",5.0e-6);
    testProcedure(taylorSimplex::eta2_234,linearization::eta2_234,
		  domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		  "taylorSimplex::eta2_234",5.0e-6);
    testProcedure(taylorSimplex::eta2_456,linearization::eta2_456,
		  domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		  "taylorSimplex::eta2_456",5.0e-6);
    
  }
  
  
  /*test +,*,evalf,tangentAt */{
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    domain z(4.11,4.22,4.33,4.44,4.55,4.66);
    taylorFunction f = taylorSimplex::x1*"17" + taylorSimplex::x2*"2";
    taylorInterval t = f.evalf(x,z);
    if (!epsilonClose(t.upperBound(),"78.31",1.0e-13))
      cout << " t.upperBound() = " << t.upperBound() << endl;
    if (!epsilonClose(t.lowerBound(),"78.1",1.0e-13))
      cout << " t.lowerBound() = " << t.lowerBound() << endl;
    if (!epsilonClose(t.upperPartial(0),"17",1.0e-15))
      cout << " t.upperPartial(0)= " << t.upperPartial(0) << endl;
    if (!epsilonClose(t.lowerPartial(0),"17",1.0e-15))
      cout << " t.lowerPartial(0)= " << t.lowerPartial(0) << endl;
    if (!epsilonClose(t.upperPartial(1),"2",1.0e-15))
      cout << " t.upperPartial(1)= " << t.upperPartial(1) << endl;
    if (!epsilonClose(t.lowerPartial(1),"2",1.0e-15))
      cout << " t.lowerPartial(1)= " << t.lowerPartial(1) << endl;
    lineInterval L = f.tangentAt(x);
    if (!epsilonClose(L.hi(),"78.1",1.0e-13))
      cout << " L.hi() = " << L.hi() << endl;
    if (!epsilonClose(L.low(),"78.1",1.0e-13))
      cout << " L.low() = " << L.low() << endl;
    if (!epsilonClose(17,L.partial(0),1.0e-15))
      cout << " L.partial(0)= " << L.partial(0) << endl;
    if (!epsilonClose(2,L.partial(1),1.0e-15))
      cout << " L.partial(1)= " << L.partial(1) << endl;
  }
  
  
  /*test plus,scale,center,upperBound,lowerBound,&partials*/ {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    domain z(4.11,4.22,4.33,4.44,4.55,4.66);
    taylorInterval t1 = taylorSimplex::x1.evalf(x,z);
    taylorInterval t2 = taylorSimplex::x2.evalf(x,z);
    taylorInterval s1 = taylorInterval::scale(t1,interval("17"));
    taylorInterval s2 = taylorInterval::scale(t2,interval("2"));
    taylorInterval t = taylorInterval::plus(s1,s2);
    if (!epsilonClose(t.upperBound(),"78.31",1.0e-13))
      cout << " t.upperBound() = " << t.upperBound() << endl;
    if (!epsilonClose(t.lowerBound(),"78.1",1.0e-13))
      cout << " t.lowerBound() = " << t.lowerBound() << endl;
    if (!epsilonClose(t.upperPartial(0),"17",1.0e-15))
      cout << " t.upperPartial(0)= " << t.upperPartial(0) << endl;
    if (!epsilonClose(t.lowerPartial(0),"17",1.0e-15))
      cout << " t.lowerPartial(0)= " << t.lowerPartial(0) << endl;
    if (!epsilonClose(t.upperPartial(1),"2",1.0e-15))
      cout << " t.upperPartial(1)= " << t.upperPartial(1) << endl;
    if (!epsilonClose(t.lowerPartial(1),"2",1.0e-15))
      cout << " t.lowerPartial(1)= " << t.lowerPartial(1) << endl;
    lineInterval c = t.tangentVectorOf();
    if (!epsilonClose(c.hi(),"78.205",1.0e-13))
      cout << " c.hi() = " << c.hi() << endl;
    if (!epsilonClose(c.low(),"78.205",1.0e-13))
      cout << " c.low() = " << c.low() << endl;
    if (!epsilonClose(17,c.partial(0),1.0e-15))
      cout << " c.partial(0)= " << c.partial(0) << endl;
    if (!epsilonClose(2,c.partial(1),1.0e-15))
      cout << " c.partial(1)= " << c.partial(1) << endl;
  }
  
  
  /*test x1*/  {
    int i,j;
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    domain z(4.11,4.22,4.33,4.44,4.55,4.66);
    char zz[6][30]={"4.11","4.22","4.33","4.44","4.55","4.66"};
    char xx[6][30]={"4.1","4.2","4.3","4.4","4.5","4.6"};
    for (j=0;j<6;j++) {
      taylorInterval t = taylorSimplex::x1.evalf(x,z);
      switch (j)
	{
	case 0 : t = taylorSimplex::x1.evalf(x,z); break;
	case 1 : t = taylorSimplex::x2.evalf(x,z); break;
	case 2 : t = taylorSimplex::x3.evalf(x,z); break;
	case 3 : t = taylorSimplex::x4.evalf(x,z); break;
	case 4 : t = taylorSimplex::x5.evalf(x,z); break;
	case 5 : t = taylorSimplex::x6.evalf(x,z); break;
	}
      if (!epsilonClose(t.upperBound(),zz[j],1.0e-14))
	cout << "x" << j+1 << "+ fails " << t.upperBound() << endl;
      if (!epsilonClose(t.lowerBound(),xx[j],1.0e-14))
	cout << "x" << j+1 << "- fails " << t.lowerBound() << endl;
      for (i=0;i<6;i++) {
	if (!epsilonClose(t.upperPartial(i),i==j ? "1" : "0",1.0e-15))
	  cout << "x" << j+1 << "++ fails " << i 
	       << " " << t.upperPartial(i) << endl;
	if (!epsilonClose(t.lowerPartial(i),i==j ? "1" : "0",1.0e-15))
	  cout << "x" << j+1 << "-- fails " << i 
	       << " " << t.lowerPartial(i) << endl;
      }
    }
  }
  
  /*test y1*/  {
    int i,j;
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    domain z(4.11,4.22,4.33,4.44,4.55,4.66);
    char zz[6][30]={"4.11","4.22","4.33","4.44","4.55","4.66"};
    char xx[6][30]={"4.1","4.2","4.3","4.4","4.5","4.6"};
    for (j=0;j<6;j++) {
      taylorInterval t = taylorSimplex::x1.evalf(x,z);
      switch (j)
	{
	case 0 : t = taylorSimplex::y1.evalf(x,z); break;
	case 1 : t = taylorSimplex::y2.evalf(x,z); break;
	case 2 : t = taylorSimplex::y3.evalf(x,z); break;
	case 3 : t = taylorSimplex::y4.evalf(x,z); break;
	case 4 : t = taylorSimplex::y5.evalf(x,z); break;
	case 5 : t = taylorSimplex::y6.evalf(x,z); break;
	}
      if (!epsilonClose(t.upperBound(),interMath::sqrt(interval(zz[j])),1.0e-4))
	cout << "x" << j+1 << "+ fails " << t.upperBound() << endl;
      if (!epsilonClose(t.lowerBound(),interMath::sqrt(interval(xx[j])),1.0e-5))
	cout << "x" << j+1 << "- fails " << t.lowerBound() << endl;
      static interval half("0.5");
      for (i=0;i<6;i++) {
	if (!epsilonClose(t.upperPartial(i),i==j ? 
			  half/interMath::sqrt(interval(xx[j])) : interval("0"),1.0e-5))
	  cout << "x" << j+1 << "++ fails " << i 
	       << " " << t.upperPartial(i) << endl;
	if (!epsilonClose(t.lowerPartial(i),i==j ? 
			  half/interMath::sqrt(interval(zz[j])) : interval("0"),1.0e-4))
	  cout << "x" << j+1 << "-- fails " << i 
	       << " " << t.lowerPartial(i) << endl;
      }
    }
  }
  
  /*test unit*/  {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    domain z(4.11,4.22,4.33,4.44,4.55,4.66);
    taylorInterval t = taylorSimplex::unit.evalf(x,z);
    if ((!t.upperBound()==1) || (!t.lowerBound()==1))
      cout << "unit fails = " << t.upperBound()<<" " << t.lowerBound()<<endl;
    for (int i=0;i<6;i++) if ((t.upperPartial(i)!=0)||(t.lowerPartial(i)!=0))
			    cout << "unitp fails = " << t.upperPartial(i)<<" " << t.lowerPartial(i)<<endl;
  }

  /* test volx */   {
    
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=1.0661359356729956;
    double mathValueD[6]={0.0716828019335723,0.06608105639401098,
   0.05995821824611842,0.06249854471173341,0.05728761862842055,
			       0.05155559993677649};
    taylorInterval at = taylorSimplex::vol_x.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "volx  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "volx D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test dih4 */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=1.1816295663326204;
    double mathValueD[6]={0.1639579615001743,-0.04682400379844412,
   -0.05202995747407655,0.050900945512886715,-0.04971942136745523,
			  -0.0547966898177983};
    taylorInterval at = taylorSimplex::dih4.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "dih4  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "dih4 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test dih5 */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=1.2130685583865823;
    double mathValueD[6]={-0.04745584218563276,0.16581065263975656,
   -0.05752859201151561,-0.050281240571535483,0.0540659685457473,
			  -0.060113530960320245};
    taylorInterval at = taylorSimplex::dih5.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "dih5  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "dih5 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test dih6 */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=1.2471258394979472;
    double mathValueD[6]={-0.05343065929090237,-0.05829075337080253,
   0.16764287016855614,-0.05602822987514417,-0.06077778903656598,
			  0.05718408426966532};
    taylorInterval at = taylorSimplex::dih6.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "dih6  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "dih6 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  
  /* test hasDeltaDenom */ {
    taylorFunction F1 = taylorSimplex::y1 + taylorSimplex::dih2;
    if (!F1.hasDeltaDenom()) cout << "hasDeltaDenom fails 1" << endl;
    taylorFunction F2 (taylorSimplex::y2);
    if (F2.hasDeltaDenom()) cout << "hasDeltaDenom fails 2" << endl;
    taylorFunction F3( taylorSimplex::dih);
    if (!F3.hasDeltaDenom()) cout << "hasDeltaDenom fails 3" << endl;
  }
  
  /* test primitiveC1 */  {
    primitiveC cD (&taylorSimplex::dih,
		   &taylorSimplex::x2,&taylorSimplex::x3,&taylorSimplex::x1,
		   &taylorSimplex::x5,&taylorSimplex::x6,&taylorSimplex::x4);
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    domain w(0.0,0.0,0.0,0.0,0.0,0.0);
    taylorInterval t = cD.evalf4(w,x,x,x); //dih2alt
    taylorInterval u = taylorSimplex::dih2.evalf4(w,x,x,x);
    if (!epsilonClose(t.upperBound(),u.tangentVectorOf().f,1.0e-8))
      cout << "cD  fails " << t.upperBound() << endl;
    if (!epsilonClose(t.lowerBound(),u.tangentVectorOf().f,1.0e-8))
      cout << "cD fails lB "  << t.lowerBound() << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonClose(t.upperPartial(i),u.tangentVectorOf().Df[i],1.0e-15))
	cout << "cD " << i << "++ fails " << t.upperPartial(i) << endl;
      if (!epsilonClose(t.lowerPartial(i),u.tangentVectorOf().Df[i],1.0e-15))
	cout << "cDl fails " << i 	<< " " << t.lowerPartial(i) << endl;
    }
  }
  
  /* test primitiveC sums */   {
    primitiveC cdih2 (&taylorSimplex::dih,
		      &taylorSimplex::x2,&taylorSimplex::x3,&taylorSimplex::x1,
		      &taylorSimplex::x5,&taylorSimplex::x6,&taylorSimplex::x4);
    primitiveC cdih3 (&taylorSimplex::dih,
		      &taylorSimplex::x3,&taylorSimplex::x1,&taylorSimplex::x2,
		      &taylorSimplex::x6,&taylorSimplex::x4,&taylorSimplex::x5);
    taylorFunction cD = taylorFunction::taylorFunction(&cdih2) + taylorFunction::taylorFunction(&cdih3) * "5.6";           
    
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    domain w(0.0,0.0,0.0,0.0,0.0,0.0);
    taylorInterval t = cD.evalf4(w,x,x,x); // dih2 + 5.6 dih3;
    
    taylorInterval udih2 = taylorSimplex::dih2.evalf4(w,x,x,x);
    taylorInterval udih3 = taylorSimplex::dih3.evalf4(w,x,x,x);
    taylorInterval uD = taylorInterval::plus(udih2,taylorInterval::scale(udih3,"5.6"));
    
    if (!epsilonClose(t.upperBound(),uD.tangentVectorOf().f,1.0e-8))
      cout << "cD  fails " << t.upperBound() << endl;
    if (!epsilonClose(t.lowerBound(),uD.tangentVectorOf().f,1.0e-8))
      cout << "cD fails lB "  << t.lowerBound() << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonClose(t.upperPartial(i),uD.tangentVectorOf().Df[i],1.0e-12))
	cout << "cD " << i << "++ fails " << t.upperPartial(i) << endl;
      if (!epsilonClose(t.lowerPartial(i),uD.tangentVectorOf().Df[i],1.0e-12))
	cout << "cDl fails " << i 	<< " " << t.lowerPartial(i) << endl;
    }
  }
  
  /* test primitiveC mixed sums */   {
    primitiveC cdih2 (&taylorSimplex::dih,
		      &taylorSimplex::x2,&taylorSimplex::x3,&taylorSimplex::x1,
		      &taylorSimplex::x5,&taylorSimplex::x6,&taylorSimplex::x4);
    primitiveC cdih3 (&taylorSimplex::dih,
		      &taylorSimplex::x3,&taylorSimplex::x1,&taylorSimplex::x2,
		      &taylorSimplex::x6,&taylorSimplex::x4,&taylorSimplex::x5);
    taylorFunction tdih2(&cdih2);
    taylorFunction tdih3(&cdih3);
    taylorFunction a = tdih2 + taylorSimplex::dih3 * "5.6";           
    taylorFunction b = taylorSimplex::dih2 + tdih3 * "5.6";
    taylorFunction c = taylorSimplex::dih2 + taylorSimplex::dih3 * "5.6";
    
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    domain w(0.0,0.0,0.0,0.0,0.0,0.0);
    taylorInterval at = a.evalf4(w,x,x,x); // dih2 + 5.6 dih3;
    taylorInterval bt = b.evalf4(w,x,x,x); // dih2 + 5.6 dih3;
    taylorInterval ct = c.evalf4(w,x,x,x); 
    
    if (!epsilonClose(at.upperBound(),bt.tangentVectorOf().f,1.0e-8))
      cout << "at  fails " << endl;
    if (!epsilonClose(at.upperBound(),ct.tangentVectorOf().f,1.0e-8))
      cout << "ct  fails " << endl;
    if (!epsilonClose(at.lowerBound(),bt.tangentVectorOf().f,1.0e-8))
      cout << "aD fails lB "  << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonClose(at.upperPartial(i),bt.tangentVectorOf().Df[i],1.0e-12))
	cout << "aD " << i << "++ fails " << bt.upperPartial(i) << endl;
      if (!epsilonClose(at.lowerPartial(i),bt.tangentVectorOf().Df[i],1.0e-12))
	cout << "aDl fails " << i << endl;
    }


    
    lineInterval al = a.tangentAt(x);
    lineInterval bl = b.tangentAt(x);
    lineInterval cl = c.tangentAt(x);
    //Mathematica values.
    double p[6]={-0.38640611319175094,-0.30583249983684146,
		 0.2592175068905934 ,
		 -0.3337851812245894,-0.1547313284571169,0.8519721867862138};
    if (!epsilonClose(interMath::sup(al.f),bl.f,1.0e-8))
      cout << "at'  fails " << endl;
    if (!epsilonClose(interMath::sup(al.f),cl.f,1.0e-8))
      cout << "ct'  fails " << endl;
    if (!epsilonClose(8.419942742042776,bl.f,1.0e-8))
      cout << "aD' fails lB "  << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonClose(interMath::sup(al.Df[i]),bl.Df[i],1.0e-12))
	cout << "aD' " << i << "++ fails "  << endl;
      if (!epsilonClose(interMath::sup(al.Df[i]),bl.Df[i],1.0e-12))
	cout << "aDl' fails " << i << endl;
      if (!epsilonClose(p[i],bl.Df[i],1.0e-12))
	cout << "aDl' fails " << i << endl;
      
    }
    
  }
  
}
