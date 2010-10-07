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

namespace local {

 taylorFunction operator*(const taylorFunction& f,const taylorFunction& g) {
   return taylorFunction::product(f,g);
 };

  taylorFunction uni (const univariate& u,const taylorFunction& f) {
   return taylorFunction::uni_compose(u,f);
  };

  taylorFunction y1 = taylorSimplex::y1;
  taylorFunction y2 = taylorSimplex::y2;
  taylorFunction y3 = taylorSimplex::y3;

  taylorFunction x1 = taylorSimplex::x1;
  taylorFunction x2 = taylorSimplex::x2;
  taylorFunction x3 = taylorSimplex::x3;
  taylorFunction x4 = taylorSimplex::x4;
  taylorFunction x5 = taylorSimplex::x5;
  taylorFunction x6 = taylorSimplex::x6;

  taylorFunction delta = taylorSimplex::delta;

  static const univariate i_inv = univariate::i_inv;
  static const univariate i_matan = univariate::i_matan;
   };

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
primitiveA x1p(lineX1,setZero);

const taylorFunction taylorSimplex::x1(&::x1p);


/*implement x2 */
static lineInterval lineX2(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(1),x.getValue(1)));
  h.Df[1]=one;
  return h;
}
primitiveA x2p(lineX2,setZero);
const taylorFunction taylorSimplex::x2(&::x2p);

/*implement x3 */
static lineInterval lineX3(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(2),x.getValue(2)));
  h.Df[2]=one;
  return h;
}
primitiveA x3p(lineX3,setZero);
const taylorFunction taylorSimplex::x3(&::x3p);

/*implement x4 */
static lineInterval lineX4(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(3),x.getValue(3)));
  h.Df[3]=one;
  return h;
}
primitiveA x4p(lineX4,setZero);
const taylorFunction taylorSimplex::x4(&::x4p);

/*implement x5 */
static lineInterval lineX5(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(4),x.getValue(4)));
  h.Df[4]=one;
  return h;
}
primitiveA x5p(lineX5,setZero);
const taylorFunction taylorSimplex::x5(&::x5p);

/*implement x6 */
static lineInterval lineX6(const domain& x)
{
  static const interval one("1");
  lineInterval h(interval(x.getValue(5),x.getValue(5)));
  h.Df[5]=one;
  return h;
}
primitiveA x6p(lineX6,setZero);
const taylorFunction taylorSimplex::x6(&::x6p);

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
  //static const interval one("1");
  lineInterval h(interval(x.getValue(0),x.getValue(0)) * 
		 interval(x.getValue(1),x.getValue(1)));
  h.Df[0]= interval(x.getValue(1),x.getValue(1));
  h.Df[1]= interval(x.getValue(0),x.getValue(0));
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

/*implement rad2*/
static int setAbsRad2(const domain& x, const domain& z, double DD[6][6]) {
  double  X[6],Z[6];
  int i;
  double DD1[6][6], DD2[6][6];
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  int r1 = secondDerive::setAbsEta2_x_126(X,Z,DD1);
  int r2 = secondDerive::setChi2over4uDelta(X,Z,DD2);
  interMath::up();
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) { DD[i][j] = DD1[i][j] + DD2[i][j]; }
  if (r1+r2) { testAbs(DD,"setAbsDihedral"); }
  return r1+r2;
}
primitiveA rad2Primitive(linearization::rad2,setAbsRad2);
const taylorFunction taylorSimplex::rad2(&::rad2Primitive);

/*implement delta_x4*/
static int setAbsDeltaX4(const domain& x,const domain& z,double DDf[6][6]) {
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) { DDf[i][j]= 2.0; }
  // all second partials are pm 0,1,2.  
}
primitiveA deltax4Primitive(linearization::delta_x4,setAbsDeltaX4);
const taylorFunction taylorSimplex::delta_x4(&::deltax4Primitive);


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

const taylorFunction taylorSimplex::dih2 = taylorFunction::rotate2(taylorSimplex::dih);
const taylorFunction taylorSimplex::dih3 = taylorFunction::rotate3(taylorSimplex::dih);
const taylorFunction taylorSimplex::dih4 = taylorFunction::rotate4(taylorSimplex::dih);
const taylorFunction taylorSimplex::dih5 = taylorFunction::rotate5(taylorSimplex::dih);
const taylorFunction taylorSimplex::dih6 = taylorFunction::rotate6(taylorSimplex::dih);


/*implement dih2*/
/*
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
*/

/*implement dih3*/
/*
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
*/

/*implement dih4 : |- dih4_y y1 y2 y3 y4 y5 y6 = dih_y y4 y2 y6 y1 y5 y3 */ 
/*
primitiveC dih4Primitive
(&taylorSimplex::dih,
  &taylorSimplex::x4  , &taylorSimplex::x2, &taylorSimplex::x6,
  &taylorSimplex::x1 , &taylorSimplex::x5, &taylorSimplex::x3);
const taylorFunction taylorSimplex::dih4(&::dih4Primitive);
*/

/*implement dih5 : |- dih5_y y1 y2 y3 y4 y5 y6 = dih_y y5 y1 y6 y2 y4 y3 */
/*
primitiveC dih5Primitive
(&taylorSimplex::dih,
  &taylorSimplex::x5  , &taylorSimplex::x1, &taylorSimplex::x6,
  &taylorSimplex::x2 , &taylorSimplex::x4, &taylorSimplex::x3);
const taylorFunction taylorSimplex::dih5(&::dih5Primitive);
*/

/*implement dih6 : |- dih6_y y1 y2 y3 y4 y5 y6 = dih_y y6 y1 y5 y3 y4 y2 */
/*
primitiveC dih6Primitive
(&taylorSimplex::dih,
  &taylorSimplex::x6  , &taylorSimplex::x1, &taylorSimplex::x5,
  &taylorSimplex::x3 , &taylorSimplex::x4, &taylorSimplex::x2);
const taylorFunction taylorSimplex::dih6(&::dih6Primitive);
*/

/*implement rhazim*/
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

/*implement rhazim2 ... */
const taylorFunction taylorSimplex::rhazim2 = 
  taylorFunction::rotate2(taylorSimplex::rhazim);
const taylorFunction taylorSimplex::rhazim3 = 
  taylorFunction::rotate3(taylorSimplex::rhazim);

/*
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
*/

/*implement azim3*/
/*
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
*/

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

/* implement halfbump_x (univariate) */
/*
 |- !x. &0 <= x
         ==> halfbump_x x =
             --(&4398119 / &2376200) +
             &17500 / &11881 * sqrt x - &31250 / &106929 * x
*/
static interval a0("-4398119");
static interval b0("2376200");
static interval a1("17500");
static interval b1("11881");
static interval a2("-31250");
static interval b2("106929");
univariate i_halfbump_x = univariate::i_pow0 * (a0 / b0) +
  univariate::i_sqrt * (a1 / b1) + univariate::i_pow1 * (a2 / b2);
static primitive_univariate i_halfbump1P(::i_halfbump_x,0);
static primitive_univariate i_halfbump4P(::i_halfbump_x,3);
const taylorFunction taylorSimplex::halfbump_x1(&::i_halfbump1P);
const taylorFunction taylorSimplex::halfbump_x4(&::i_halfbump4P);

/* implement marchalQuartic (univariate) */
// marchalQuartic[Sqrt[x]/2] = 
/* deprecated: 
static interval m0("-8.3439434337479413233");
static interval m1("29.738910202367943669");
static interval m2("-24.647762183814337061");
static interval m3("7.7264705379397797225");
static interval m4("-0.83466203370305222185");
univariate i_marchalQ = univariate::i_pow0 * m0 +
  univariate::i_sqrt * m1 +
  univariate::i_pow1 * m2 +
  univariate::i_pow3h2 * m3 +
  univariate::i_pow2 * m4;
static primitive_univariate i_marchalQprim(::i_marchalQ,0);
static taylorFunction marchalQ(&::i_marchalQprim);
const taylorFunction taylorSimplex::marchalDih = taylorFunction::product(marchalQ,taylorSimplex::dih);
const taylorFunction taylorSimplex::marchalDih2 = taylorFunction::rotate2(taylorSimplex::marchalDih);
const taylorFunction taylorSimplex::marchalDih3 = taylorFunction::rotate3(taylorSimplex::marchalDih);
const taylorFunction taylorSimplex::marchalDih4 = taylorFunction::rotate4(taylorSimplex::marchalDih);
const taylorFunction taylorSimplex::marchalDih5 = taylorFunction::rotate5(taylorSimplex::marchalDih);
const taylorFunction taylorSimplex::marchalDih6 = taylorFunction::rotate6(taylorSimplex::marchalDih);
*/


/* implement gchi (univariate) */ 
// gchi (sqrt x) = &4 * mm1 / pi -(&504 * mm2 / pi)/ &13 +(&200 * (sqrt x) * mm2 /pi)/ &13
static interval i_gchi_c0("0.974990367692870754241952463595");
static interval i_gchi_c1("0.124456752559607807811255454313");
univariate i_gchi = univariate::i_sqrt* i_gchi_c1 + univariate::i_pow0 * i_gchi_c0;
/*implement gchi1_x x1 x2 x3 x4 x5 x6 = gchi (sqrt x1) * dih_x x1 x2 x3 x4 x5 x6; */
static primitive_univariate i_gchi1P(::i_gchi, 0 );

static taylorFunction i_gchi1(&::i_gchi1P);


static primitiveC gchi1XPrim
(&::x1x2,
  &::i_gchi1  , &taylorSimplex::dih, &taylorSimplex::unit,
  &taylorSimplex::unit , &taylorSimplex::unit, &taylorSimplex::unit);
const taylorFunction taylorSimplex::gchi1_x(&::gchi1XPrim);

const taylorFunction taylorSimplex::gchi2_x = taylorFunction::rotate2(taylorSimplex::gchi1_x);
const taylorFunction taylorSimplex::gchi3_x = taylorFunction::rotate3(taylorSimplex::gchi1_x);
const taylorFunction taylorSimplex::gchi4_x = taylorFunction::rotate4(taylorSimplex::gchi1_x);
const taylorFunction taylorSimplex::gchi5_x = taylorFunction::rotate5(taylorSimplex::gchi1_x);
const taylorFunction taylorSimplex::gchi6_x = taylorFunction::rotate6(taylorSimplex::gchi1_x);

/*implement eta2_126*/
static int setEta2_126(const domain& x,const domain& z,double DD[6][6])
{
  double xa[6],za[6];
  for (int i=0;i<6;i++) {
    xa[i] = x.getValue(i);
    za[i] = z.getValue(i);
  }
  secondDerive::setAbsEta2_x_126(xa,za,DD);
  return 1;
}
primitiveA eta2Primitive(linearization::eta2_126,setEta2_126);
const taylorFunction taylorSimplex::eta2_126(&::eta2Primitive);

/*implement eta2_135*/
static primitiveC eta2_135_Primitive
(&taylorSimplex::eta2_126,
 &taylorSimplex::x1,&taylorSimplex::x3,&taylorSimplex::unit,
 &taylorSimplex::unit,&taylorSimplex::unit,&taylorSimplex::x5);
const taylorFunction taylorSimplex::eta2_135(&::eta2_135_Primitive);

/*implement eta2_234*/
static primitiveC eta2_234_Primitive
(&taylorSimplex::eta2_126,
 &taylorSimplex::x2,&taylorSimplex::x3,&taylorSimplex::unit,
 &taylorSimplex::unit,&taylorSimplex::unit,&taylorSimplex::x4);
const taylorFunction taylorSimplex::eta2_234(&::eta2_234_Primitive);

/*implement eta2_456*/
static primitiveC eta2_456_Primitive
(&taylorSimplex::eta2_126,
 &taylorSimplex::x4,&taylorSimplex::x5,&taylorSimplex::unit,
 &taylorSimplex::unit,&taylorSimplex::unit,&taylorSimplex::x6);
const taylorFunction taylorSimplex::eta2_456(&::eta2_456_Primitive);

/*implement arclength_x_123*/
//ArcCos[(x1 + x2 - x3)/(Sqrt[4 x1 x2])].
static interval mone("-1");
static interval four("4");
static taylorFunction al_num = 
  taylorSimplex::x1 + taylorSimplex::x2 + taylorSimplex::x3 * mone;
static taylorFunction x1x2_4 = ::x1x2 * four;
static taylorFunction al_den = 
  taylorFunction::uni_compose(univariate::i_sqrt,x1x2_4);
static taylorFunction al_den_inv = 
  taylorFunction::uni_compose(univariate::i_inv,al_den);
static taylorFunction a_arg = 
  taylorFunction::product(al_num,al_den_inv);
const taylorFunction taylorSimplex::arclength_x_123 = 
 taylorFunction::uni_compose(univariate::i_acos,a_arg);
  

/*implement acos_sqrt_x1 */
const taylorFunction taylorSimplex::acos_sqrt_x1 = 
  taylorFunction::uni_compose(univariate::i_acos,
			      taylorSimplex::y1);


/*implement asn797 */
static interval pi("3.1415926535897932385");
static taylorFunction asn797e = 
  taylorFunction::product
 (taylorSimplex::unit * pi,
  taylorFunction::uni_compose(univariate::i_inv,taylorSimplex::x1));
static taylorFunction sinpik =
  taylorFunction::uni_compose(univariate::i_sin,asn797e);
static interval cos797("0.69885563921392235500");
static taylorFunction asn797b = taylorFunction::product
  (taylorSimplex::unit * cos797,::sinpik);
static taylorFunction asn797a = 
  taylorFunction::uni_compose(univariate::i_asin,::asn797b);
const taylorFunction taylorSimplex::asn797k = 
  taylorFunction::product(taylorSimplex::x1,::asn797a);

/*implement asnFnhk */
// k * asn (( h * sqrt3 / #4.0 + sqrt(&1 - (h/ &2) pow 2)/ &2) * sin (pi/ k))`;;
// sinpik as above.
static taylorFunction sinpiR2 = taylorFunction::rotate2(sinpik);
static interval sqrt3("1.7320508075688772935");
static interval two ("2");
static taylorFunction asnFh = 
 taylorSimplex::x1 * (sqrt3 / four) +
  (taylorFunction::uni_compose
 (univariate::i_sqrt,
  taylorSimplex::unit + 
  (taylorFunction::uni_compose
 (univariate::i_pow2,taylorSimplex::x1 * (one /two))) * (-one)))*(one / two);
static taylorFunction asnFnhka = 
  taylorFunction::uni_compose
  (univariate::i_asin,
   taylorFunction::product(asnFh,sinpiR2));
const taylorFunction taylorSimplex::asnFnhk = 
  taylorFunction::product(taylorSimplex::x2,asnFnhka);


/*implement norm2hhx */
//(y1 - hminus - hplus)^2 + (y2 - 2)^2 + (y3 - 2)^2 + 
// (y4 - 2)^2 + (y5 - 2)^2 + (y6 - 2)^2;
static interval mfour("-4");
//static interval four("4");
static interval n0("-5.114308844180643");
static interval n1("26.539038738416085");
static univariate ym2sq = 
  univariate::i_pow1 + univariate::i_sqrt * "-4.0";
static primitive_univariate ym2sqP(ym2sq,0);
static univariate ymmsq = 
  univariate::i_pow1 + univariate::i_sqrt * n0 + univariate::i_pow0 * n1;
static primitive_univariate ymmsqP(ymmsq,0);
static taylorFunction t_ym2sq(&ym2sqP);
static taylorFunction t_ymmsq(&ymmsqP);
const taylorFunction taylorSimplex::norm2hhx =
  t_ymmsq + taylorFunction::rotate2(t_ym2sq) +
   taylorFunction::rotate3(t_ym2sq) +
  taylorFunction::rotate4(t_ym2sq) +
  taylorFunction::rotate5(t_ym2sq) +
  taylorFunction::rotate6(t_ym2sq);
 

namespace local { 
  static const taylorFunction x1cube = x1 * x1 * x1;
}
const taylorFunction taylorSimplex::x1cube = local::x1cube;


/*
`sol_euler_x_div_sqrtdelta x1 x2 x3 x4 x5 x6 = 
  (let a = sqrt(x1*x2*x3) + sqrt( x1)*(x2 + x3 - x4)/ &2 + 
     sqrt(x2)*(x1 + x3 - x5)/ &2 + sqrt(x3)*(x1 + x2 - x6)/ &2 in
     (matan ((delta_x x1 x2 x3 x4 x5 x6)/(&4 * a pow 2 )))/( a))`;;
 */

/* implement sol_euler_x_div_sqrtdelta */  

namespace local {
  static const interval half("0.5");
  static const interval four ("4");
  static const interval mone("-1");
  static const taylorFunction 
   aso (y1 * y2 * y3 + y1 * (x2 + x3 + x4 * mone)* half +
     y2 * (x1 + x3 + x5* mone) * half + y3 * (x1 + x2 + x6* mone) * half);
  static const taylorFunction sol_euler_x_div_sqrtdelta = 
   (uni(i_matan, (delta * uni(i_inv,aso * aso * four ) )) * uni(i_inv,aso));
};

const taylorFunction taylorSimplex::sol_euler_x_div_sqrtdelta = local::sol_euler_x_div_sqrtdelta;

const taylorFunction taylorSimplex::sol_euler246_x_div_sqrtdelta = taylorFunction::rotate4(taylorSimplex::sol_euler_x_div_sqrtdelta);

const taylorFunction taylorSimplex::sol_euler345_x_div_sqrtdelta = taylorFunction::rotate5(taylorSimplex::sol_euler_x_div_sqrtdelta);

const taylorFunction taylorSimplex::sol_euler156_x_div_sqrtdelta = taylorFunction::rotate6(taylorSimplex::sol_euler_x_div_sqrtdelta);


/*
static int primHasDeltaDenom(const primitive* p) {
  return
    ((p == &dih1Primitive) || (p == &dih2Primitive) || (p == &dih3Primitive) ||
     (p == &rhazimPrimitive) || (p== &rhazim2Primitive) || (p == &rhazim3Primitive) ||
     (p == &solPrimitive));
}
*/

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

taylorFunction taylorFunction::uni_compose // minor memory leak
(const univariate& f,const taylorFunction& g) {
  primitive_univariate* fp = new primitive_univariate(f,0);
  taylorFunction* fF = new taylorFunction(fp);
  taylorFunction* gF = new taylorFunction(g);
  primitive* uCp = new primitiveC
   (fF,gF,&taylorSimplex::unit,&taylorSimplex::unit,
    &taylorSimplex::unit,&taylorSimplex::unit,&taylorSimplex::unit);
  taylorFunction uc(uCp);
  return uc;
  }

taylorFunction taylorFunction::product // minor memory leak.
(const taylorFunction& f,const taylorFunction& g) {
  taylorFunction* fF = new taylorFunction(f);
  taylorFunction* gF = new taylorFunction(g);
  primitive* pp = new primitiveC(&::x1x2,fF,gF,&taylorSimplex::unit,
		&taylorSimplex::unit,&taylorSimplex::unit,&taylorSimplex::unit);
  taylorFunction prod(pp);
  return prod;
}

taylorFunction taylorFunction::compose // minor memory leak
(const taylorFunction& f,
 const taylorFunction& x1,const taylorFunction& x2,const taylorFunction& x3,
 const taylorFunction& x4, const taylorFunction& x5, const taylorFunction& x6)
{
  taylorFunction* fp = new taylorFunction(f);
  taylorFunction* x1p = new taylorFunction(x1);
  taylorFunction* x2p = new taylorFunction(x2);
  taylorFunction* x3p = new taylorFunction(x3);
  taylorFunction* x4p = new taylorFunction(x4);
  taylorFunction* x5p = new taylorFunction(x5);
  taylorFunction* x6p = new taylorFunction(x6);
  primitive* pp = new primitiveC(fp,x1p,x2p,x3p,x4p,x5p,x6p);
  taylorFunction g(pp);
  return g;
}

 taylorFunction taylorFunction::rotate2(const taylorFunction& f) {
  taylorFunction g = taylorFunction::compose
  (f,
   taylorSimplex::x2,taylorSimplex::x3,taylorSimplex::x1,
   taylorSimplex::x5,taylorSimplex::x6,taylorSimplex::x4);
  return g;
}

 taylorFunction taylorFunction::rotate3(const taylorFunction& f) {
  taylorFunction g = taylorFunction::compose
  (f,
   taylorSimplex::x3,taylorSimplex::x1,taylorSimplex::x2,
   taylorSimplex::x6,taylorSimplex::x4,taylorSimplex::x5);
  return g;
}

 taylorFunction taylorFunction::rotate4(const taylorFunction& f) {
  taylorFunction g = taylorFunction::compose
    (f,
  taylorSimplex::x4  , taylorSimplex::x2, taylorSimplex::x6,
  taylorSimplex::x1 , taylorSimplex::x5,  taylorSimplex::x3);
  return g;
}

 taylorFunction taylorFunction::rotate5(const taylorFunction& f) {
  taylorFunction g = taylorFunction::compose
    (f,
     taylorSimplex::x5  , taylorSimplex::x3, taylorSimplex::x4,
     taylorSimplex::x2 , taylorSimplex::x6, taylorSimplex::x1);
  return g;
}

 taylorFunction taylorFunction::rotate6(const taylorFunction& f) {
  taylorFunction g = taylorFunction::compose
    (f,
     taylorSimplex::x6  , taylorSimplex::x1, taylorSimplex::x5,
     taylorSimplex::x3 , taylorSimplex::x4, taylorSimplex::x2);
  return g;
}

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


/*
void taylorFunction::setReducibleState(int i)
{ reduState = i; }

int taylorFunction::getReducibleState() const
{ return reduState; }
*/

/*
int taylorFunction::hasDeltaDenom() const {
  taylorFunction u  (*this);
  for (mapPrim::const_iterator it = u.data.begin(); it!= u.data.end(); ++it) {
    primitive* p = (primitive*) (it->first);
    if (primHasDeltaDenom(p)) { return 1; } }
  return 0;
}
*/

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

  /* from univariate.cc */
    static int epsilon3(double* f,const univariate & u) {
      interval x("0.21");
      for (int i=0;i<3;i++) {
	epsilonCloseDoubles(f[i],interMath::sup(u.eval(x,i)),1.0e-8);
      }
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
    testProcedure(taylorSimplex::eta2_126,linearization::eta2_126,
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

  /* test rad2 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=1.6333363881302794;
    double mathValueD[6]={0.057786164807838214,0.05761105521751131,
   0.05741965636296806,0.06701170422099567,0.06721538721254888,
			  0.06743943850325723};
    taylorInterval at = taylorSimplex::rad2.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "rad2  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "rad2 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test delta_x4 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=1.6333363881302794;
    double mathValueD[6]={0.057786164807838214,0.05761105521751131,
   0.05741965636296806,0.06701170422099567,0.06721538721254888,
			  0.06743943850325723};
    taylorInterval at = taylorSimplex::rad2.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "delta_x4  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "delta_x4 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test marchalDih, deprecated */  
  /*  { 
    double md[3]={0.8148484787433622,12.760561387665467,-66.28061167966449};
      epsilon3(md,::i_marchalQ);
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=1.1314338321497612;
    double mathValueD[6]={-0.7804417742116788,-0.049120282260656074,
   -0.054018913876389546,0.14725412156249917,-0.042144869722190594,
      -0.04693241526153936};
    taylorInterval at = taylorSimplex::marchalDih.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "marchalDih  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "marchalDih D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
    } */

  /* test uni_compose */ {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 2.04939015319192;
    double mathValueD[6]={0,0.24397501823713327,0,0,0,0};
    taylorFunction t = taylorFunction::uni_compose(univariate::i_sqrt,taylorSimplex::x2);
    taylorInterval at = t.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "uni  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "uni D " << i << "++ fails " << at.upperPartial(i) << endl;
    }    
  }

  /* test prod */ {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 2.4623610348104914;
    double mathValueD[6]={0.40443775297783785,-0.10690140741833755,
   -0.11756239286152013,0.32047195412373986,-0.0917206840314374,
			  -0.10213991072724367};
    taylorFunction t = 
      taylorFunction::product(taylorSimplex::y1,taylorSimplex::dih);
    taylorInterval at = t.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "uni  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "uni D " << i << "++ fails " << at.upperPartial(i) << endl;
    }    
  }

  /* test arclength_x_123 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 1.0679029643628666;
    double mathValueD[6]={-0.07043519394425567,-0.07203236387496442,
			  0.13751633103402303,0,0,0};
    taylorInterval at = taylorSimplex::arclength_x_123.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "arclength_x_123  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "arclength_x_123 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test norm2hhx */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 0.33641905470850064;
    double mathValueD[6]={-0.262888552950994,0.024099927051466907,
   0.0355143556591757,0.04653741075440776,0.057190958417936553,
			  0.06749519175968627};
    taylorInterval at = taylorSimplex::norm2hhx.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "norm2hhx  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "norm2hhx D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test acos_sqrt_x1 */   { 
    domain x(0.1,0.2,0.3,0.4,0.5,0.6);
    double mValue= 1.2490457723982542;
    double mathValueD[6]={-1.6666666666666667,0,0,0,0,0};
    taylorInterval at = taylorSimplex::acos_sqrt_x1.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "acos_sqrt_x1  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "acos_sqrt_x1 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test asn797k */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 2.0742570836404837;
    double mathValueD[6]={0.0648275015403495,0,0,0,0,0};
    taylorInterval at = taylorSimplex::asn797k.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "asn797k  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "asn797k D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test asnFnhk */   { 
    domain x(1.04, 1.08, 1.12, 1.16, 1.2, 1.24);
    double mValue= 0.22005326245872275;
    double mathValueD[6]={0.07141922522392495,2.7397148354175482,0,
			  0,0,0};
    taylorInterval at = taylorSimplex::asnFnhk.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "asnFnhk  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "asnFnhk D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }



  /* test eta2_126 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 19.19;
    double mathValueD[6]={0.5999999999999996,4.3,4.499999999999999,-8.2,
			  3.700000000000001,3.8999999999999986};
    taylorInterval at = taylorSimplex::delta_x4.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "delta_x4  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "delta_x4 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test eta2_135 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=1.4343699150244082;
    double mathValueD[6]={0.10607345504918758,0,0.11054816002151685,
			  0,0.11646925805115915,0};
    taylorInterval at = taylorSimplex::eta2_135.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "eta2_135  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "eta2_135 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test eta2_234 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=1.4335919177340792;
    double mathValueD[6]={0,0.10856346275290063,0.11097076506380871,
			  0.11373888281761776,0,0};
    taylorInterval at = taylorSimplex::eta2_234.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "eta2_234  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "eta2_234 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test eta2_456 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=1.5002470762642062;
    double mathValueD[6]={0,0,0,0.10867530033135317,
			  0.11098297337542629,0.11362008143844202};
    taylorInterval at = taylorSimplex::eta2_456.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "eta2_456  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "eta2_456 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test gchi1_x */   {
      double gchid[3]={1.0320236166281522,0.135793449845905,-0.32331773772834516};
      epsilon3(gchid,::i_gchi);
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=1.4921173443920384;
      double mathValueD[6]={0.10048454642157742,-0.06477906444011666,
			    -0.07123930364273548,0.19419644576045844,-0.05557999884990159,
			    -0.06189373946233846};
    taylorInterval at = taylorSimplex::gchi1_x.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gchi1  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "gchi1 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test gchi2_x */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=1.5340569117310174;
      double mathValueD[6]={-0.06572752258736782,0.10500885807170765,
   -0.07824003437923059,-0.056271683063299445,0.19703975945664476,
   -0.06851228454381249};
    taylorInterval at = taylorSimplex::gchi2_x.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gchi2  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "gchi2 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test gchi3_x */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=1.5793842997093803;
      double mathValueD[6]={-0.07331727287522762,-0.07936025924977397,
   0.1095205207388263,-0.06342330577935136,-0.06934245768731484,
			    0.19986093458496015};
    taylorInterval at = taylorSimplex::gchi3_x.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gchi3  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "gchi3 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test gchi4_x */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=1.4605568345059332;
      double mathValueD[6]={0.20266073908760945,-0.05787695290919818,
   -0.06431178785046088,0.09797074520733327,-0.06145584263882206,
			    -0.06773161581432371};
    taylorInterval at = taylorSimplex::gchi4_x.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gchi4  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "gchi4 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test gchi5_x */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=1.502995593710665;
      double mathValueD[6]={-0.05879793125270706,0.205439897510248,
   -0.07127809859377435,-0.06229860835387361,0.10257294591611826,
			    -0.07448084572888418};
    taylorInterval at = taylorSimplex::gchi5_x.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gchi5  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "gchi5 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test gchi6_x */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=1.5488309766758375;
      double mathValueD[6]={-0.06635662384100449,-0.07239247365030564,
   0.20819909435958153,-0.06958259964677825,-0.07548117388987628,
			    0.10720235004689033};
    taylorInterval at = taylorSimplex::gchi6_x.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gchi6  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "gchi6 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test halfbump_x1 */   {
    double halfd[3]={-1.2372909856488465,1.3148592857021388,-3.8264506746765212};
      epsilon3(halfd,::i_halfbump_x);

      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue= -0.06665321364422902;
      double mathValueD[6]={0.07146660745052882,0,0,0,0,0};
    taylorInterval at = taylorSimplex::halfbump_x1.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "halfbump_x1 fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "halfbump_x1 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test halfbump_x4 */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue= -0.047139389935398804;
      double mathValueD[6]={0,0,0,0.0588482960800643,0,0};
    taylorInterval at = taylorSimplex::halfbump_x4.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "halfbump_x4  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "halfbump_x4 D " << i << "++ fails " << at.upperPartial(i) << endl;
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
    /*
    taylorFunction F1 = taylorSimplex::y1 + taylorSimplex::dih2;
    if (!F1.hasDeltaDenom()) cout << "hasDeltaDenom fails 1" << endl;
    taylorFunction F2 (taylorSimplex::y2);
    if (F2.hasDeltaDenom()) cout << "hasDeltaDenom fails 2" << endl;
    taylorFunction F3( taylorSimplex::dih);
    if (!F3.hasDeltaDenom()) cout << "hasDeltaDenom fails 3" << endl;
    */
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
