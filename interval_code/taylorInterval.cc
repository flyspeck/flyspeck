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
/*   Section:primitiveA                                                               */
/*                                                                            */
/* ========================================================================== */


class primitiveA : public primitive 
{
private:
  lineInterval (*hfn)(const domain&);
  
  // all the arrays of double [6][6] are bounds on abs value of second partials.
  int (*setAbsSecond)(const domain& x,const domain& z,double [6][6]);
  
public:
  lineInterval tangentAtEstimate(const domain& x) const { return (*hfn)(x); }
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
/*   Section:primitive_monom                                                               */
/*                                                                            */
/* ========================================================================== */


// procedures for monomial terms x1^n1 ... x6^n6 .

/*
interval mpow_i(const interval& x,int n) {
  static const interval one("1");
  static const interval zero("0");
  switch (n) {
  case 0 : return one;
  case 1 : return x;
  default : 
    if (n <0) { error::fatal("negative exponent in mpow_i");  return zero; } else
      {
	int m = n / 2;
	interval u = mpow_i(x,m);
	interval u2 = u*u;
	return ( n % 2 ? x * u2 : u2);
      }
  }
}
*/

interval mpow_i(const interval& x,int n) {
  static const interval one("1");
  static const interval zero("0");
  switch (n) {
  case 0 : return one;
  case 1 : return x;
  default : 
    if (n <0) { error::fatal("negative exponent in mpow_i");  return zero; } 
    if (interMath::inf(x) < 0.0) { error::fatal("negative base in mpow"); return zero; }
    interMath::up();
    double u = pow(interMath::sup(x),n);
    interMath::down();
    double l = pow(interMath::inf(x),n);
    interval lu(l,u);
    return lu;
  }
}

// compute x^n, n x^{n-1},

void mpow_d(const interval& x, int n, interval x_d[2]) {
  static const interval zero("0");
  static const interval one("1");
  switch (n) {
  case 0: x_d[0] = one; x_d[1]=zero; return;
  case 1: x_d[0] = x; x_d[1]=one; return;
   default: 
     if ((n < 0) || (n > 50)) { error::fatal(" exponent out of range in mpow_d"); return; } 
     interval u = mpow_i(x,n-1);
     interval ni(1.0* n,1.0* n); // N.B. for huge n, this can produce a rounding error.
     x_d[0] = x * u; x_d[1] = ni * u;
     return;
  }
}

// compute x^n, n x^{n-1}, n (n-1) x^{n-2}:

void mpow_d_dd(const interval& x, int n, interval x_d_dd[3]) {
  static const interval zero("0");
  static const interval one("1");
  static const interval two("2");
  for (int i =0;i<3;i++) { x_d_dd[i]=zero; }
  switch (n) {
  case 0: x_d_dd[0] = one; return;
  case 1: x_d_dd[0] = x; x_d_dd[1]=one; return;
  case 2: x_d_dd[0] = x*x; x_d_dd[1]=two * x; x_d_dd[2] = two; return;
  default: 
    if ((n < 0) || (n > 50)) { error::fatal("exponent range in mpow_d_dd"); return; } 
    interval u = mpow_i(x,n-2);
    interval ni(1.0* n,1.0* n); // N.B. for huge n, this can produce a rounding error.
    interval mi(n-1.0,n-1.0);
    interval xu = x * u;
    x_d_dd[0] = x * xu;  x_d_dd[1] = ni * xu;  x_d_dd[2]= ni * mi * u;
    return;
  }
}

// 
static const lineInterval tangent_of_monom(const domain& w,const int n[6]) {
  static const interval one("1");
  lineInterval t;
  t.f = one;
  for (int j=0;j<6;j++) { t.Df[j] = one; };
  for (int i=0;i<6;i++) {
    double w0 = w.getValue(i);
    interval x(w0,w0);
    interval y[2];
    mpow_d(x,n[i],y);
    t.f = t.f * y[0];
    for (int j=0;j<6;j++)  { t.Df[j] = t.Df[j] * (i==j ? y[1] : y[0]);    }
  }
  return t;
}

static const taylorInterval taylor_of_monom(const domain& w,const domain& x,
					    const domain& y,const domain& z,const int n[6]) {
  static const interval one("1");
  static const interval zero("0");
  interval DDw[6][6];
  
  // initialize
  int nz = 0;
  int p[6];
  for (int i=0;i<6;i++) if (n[i]>0) { p[nz] = i; nz ++; }
  for (int j=0;j<6;j++) for (int k=0;k<6;k++) { DDw[j][k]=zero; }
  for (int j=0;j<nz;j++) for (int k=0;k<nz;k++) { DDw[p[j]][p[k]]=one; }
  interval r[6][3];
  for (int i=0;i<6;i++) { 
    interval xz(x.getValue(i),z.getValue(i));
    mpow_d_dd(xz,n[i],r[i]); 
  }
  // calculate second derivatives
  for (int j=0;j<nz;j++) for (int k=0;k<nz;k++) for (int i=0;i<nz;i++) {
	if ((i!=j) && (i != k)) { DDw[p[j]][p[k]] = DDw[p[j]][p[k]] * r[p[i]][0]; }
      }
  for (int i=0;i<nz;i++) { DDw[p[i]][p[i]] = DDw[p[i]][p[i]] * r[p[i]][2]; }
  for (int j=0;j<nz;j++) 
    for (int k=0;k<nz;k++) 
      if (j!=k) {
	DDw[p[j]][p[k]] = DDw[p[j]][p[k]] * (r[p[j]][1] * r[p[k]][1]);
      }
  double DD[6][6];
  intervalToAbsDouble(DDw,DD);
  lineInterval tangentVector = tangent_of_monom(y,n);
  return taylorInterval(tangentVector,w,DD);
}

class primitive_monom : public primitive 
{
private:
  int n[6];
  
public:
  lineInterval tangentAtEstimate(const domain& x) const { return tangent_of_monom(x,n); }
  taylorInterval evalf4(const domain& w,const domain& x,
			const domain& y,const domain& z) const {
    return taylor_of_monom(w,x,y,z,n);
  }
  primitive_monom(const int [6]);
};

primitive_monom::primitive_monom(const int m[6])
{
  for (int i=0;i<6;i++) { n[i] = m[i]; }
}


/* ========================================================================== */
/*                                                                            */
/*   Section:primitive_univariate                                                     */
/*                                                                            */
/* ========================================================================== */


class primitive_univariate : public primitive 
{
private:
  int slot;
  const univariate* f;
  
public:
  
  lineInterval tangentAtEstimate(const domain& x) const ;
  
  taylorInterval evalf4(const domain& w,const domain& x,
			const domain& y,const domain& z) const;
  
  primitive_univariate(const univariate&x, int slot0 ) { f = &x; slot = slot0; };
};

lineInterval primitive_univariate::tangentAtEstimate(const domain& x) const {
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
  taylorInterval a(primitive_univariate::tangentAtEstimate(y),w,DD);
  return a;
}

/* ========================================================================== */
/*                                                                            */
/*   Section:primitiveC  composites                                                   */
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
  
  lineInterval tangentAtEstimate(const domain& x) const ;
  
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

lineInterval primitiveC::tangentAtEstimate(const domain& x) const
{
  if (!hdr) { error::fatal ("tangentAtEstimate: function expected, returning 0");   }
  lineInterval pv[6];
  pv[0] = p1->tangentAtEstimate(x);
  pv[1] = p2->tangentAtEstimate(x);
  pv[2] = p3->tangentAtEstimate(x);
  pv[3] = p4->tangentAtEstimate(x);
  pv[4] = p5->tangentAtEstimate(x);
  pv[5] = p6->tangentAtEstimate(x);
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
  double aw[6], bw[6];
  for (int i =0;i<6;i++) {
    aw[i] = pv[i].lowerBound(); bw[i] = pv[i].upperBound(); 
  }

  // calculate narrow value range of pv[i].
  double a[6],b[6];
  for (int i=0;i<6;i++) {
    a[i]=pv[i].tangentVectorOf().low(); b[i] =pv[i].tangentVectorOf().hi();
  }
  
  // choose an expansion point u near p(y), and widths wu for image of p1,...,p6 under y
  double u[6],wu[6],wf[6];
  interMath::up();
  for (int i=0;i<6;i++) {
    u[i] =(b[i] + a[i] )/2.0;
    wf[i] = max(b[i]-u[i],u[i]-a[i]);  // narrow w
    wu[i] = max(bw[i]-u[i],u[i]-aw[i]); // wide w.
  }
  taylorInterval fu = hdr->evalf4(wu,aw,u,bw);

  // now compute interval tangentVector of f (at exact point p(y) as opposed to approximation u)
  lineInterval fpy;
  {
    taylorInterval t(fu.tangentVectorOf(),wf,fu.DD); // narrow adjustment from p(y) to u.
    interval v(t.lowerBound(),t.upperBound());
    fpy.f = v;
    for (int i=0;i<6;i++)  {
      interval r(t.lowerPartial(i),t.upperPartial(i));
      fpy.Df[i] = r;
    }
  }

  // apply chain rule to compute narrow first derivative data.
  lineInterval lin;  {
    lin.f = fpy.f;
  static interval zero("0");
  for (int i=0;i<6;i++)     lin.Df[i] = zero; 
  for (int j=0;j<6;j++) {
    if ((fpy.Df[j].zero())) continue;
    for (int i=0;i<6;i++)
      {
	interval r = pv[j].tangentVectorOf().partial(i);
	if (!(r.zero()))
	  lin.Df[i]  = lin.Df[i] + fpy.Df[j] * r;
      }
  }}

  // initialize second derivative data.
  double fW_partial_dabs[6]; // abs value of wide partials (over entire domain)
  double pW_partial_dabs[6][6]; // abs of function p i, partial j.
  for (int i=0;i<6;i++) {
    interval tW(fu.lowerPartial(i),fu.upperPartial(i));
    fW_partial_dabs[i] = dabs( tW);
    for (int j=0;j<6;j++) {
      interval uW(pv[i].lowerPartial(j),pv[i].upperPartial(j));
      pW_partial_dabs[i][j] = dabs(uW);
    }
  }

  // apply chain rule to compute bound on second derivative data. 
  // This is the "wide" part of the calc.
  // Often, many terms in the 4-nested loop are zero.
  double DcW[6][6];
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) { DcW[i][j]= 0.0; }
  interMath::up();
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      for (int k=0;k<6;k++) {
	if (pv[k].DD[i][j] != 0.0) 
	  DcW[i][j] = DcW[i][j] +  fW_partial_dabs[k] * pv[k].DD[i][j];
      }}
  int Nki = 0;
  int Nmj = 0;
  int kk[36], ii[36], jj[36], mm[36];
  double rki[36], rmj[36];
  for (int i=0;i<6;i++) for (int k=0;k<6;k++) {
      if (!(0.0==pW_partial_dabs[k][i])) {
      rki[Nki] = pW_partial_dabs[k][i]; kk[Nki]= k; ii[Nki]= i; Nki++;
      if (Nki > 36) { error::fatal("Nki out of range "); }
      }}
  for (int j=0;j<6;j++)  for (int m=0;m<6;m++) {
      if (!(0.0==pW_partial_dabs[m][j])) {
      rmj[Nmj] = pW_partial_dabs[m][j]; mm[Nmj]= m; jj[Nmj]= j; Nmj++;
      if (Nmj > 36) { error::fatal("Nmj out of range "); }
      }}
  interMath::up();
  for (int ki=0;ki<Nki;ki++) 
    for (int mj=0;mj<Nmj;mj++) 
      { DcW[ii[ki]][jj[mj]] = DcW[ii[ki]][jj[mj]] + fu.DD[kk[ki]][mm[mj]] * rki[ki] * rmj[mj];    }

  // debug: 
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      if (fu.DD[i][j]<0.0) { cout << endl << i << " " << j << " " << fu.DD[i][j] << endl;
	error::fatal("DD neg fu.DD in primitive C"); }
    }
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) for (int k=0;k<6;k++) { 
	if (pv[k].DD[i][j]<0.0) { cout << endl << i << " " << j << " " << k << " " << pv[k].DD[i][j]  << endl;
	error::fatal("DD neg pv[].DD in primitive C"); }
    }
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      if (DcW[i][j]<0.0) { cout << endl<<  i << " " << j << " " << Nki << " " << Nmj << " " << DcW[i][j] << endl;
	error::fatal("DD neg in primitive C"); }
    }

  // wrapup.
  taylorInterval ch(lin,w,DcW);
  return ch;
};


/* ========================================================================== */
/*                                                                            */
/*   Section:taylorSimplex                                                            */
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

/* implement monomial */
const taylorFunction taylorSimplex::monomial(int i1,int i2,int i3,int i4,int i5,int i6) {
  int n[6]={i1,i2,i3,i4,i5,i6};
  primitive* pp = new primitive_monom(n); // minor memory leak
  taylorFunction g(pp);
  return g;
}

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


/*implement chi126 */
static int setAbsChi126(const domain& x,const domain& z,double DD[6][6])
{
  double X[6],Z[6];
  interval DDh[6][6];
  int i;
  for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
  secondDerive::setChi126(X,Z,DDh);
  intervalToAbsDouble(DDh,DD);
  testAbs(DD,"setAbsChi126");
  return 1;
}
primitiveA chi126Primitive(linearization::chi126,setAbsChi126);
static const taylorFunction chi126(&::chi126Primitive);


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
  if (r1+r2) { testAbs(DD,"setAbsRad2"); }
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

/* ========================================================================== */
/*                                                                            */
/*   Section:taylorSimplex local namespace                                            */
/*                                                                            */
/* ========================================================================== */


namespace local {

 taylorFunction operator*(const taylorFunction& f,const taylorFunction& g) {
   return taylorFunction::product(f,g);
 };

  taylorFunction uni(const univariate& u,const taylorFunction& f) {
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
  taylorFunction delta_x4 = taylorSimplex::delta_x4;
  taylorFunction dih = taylorSimplex::dih;
  taylorFunction unit = taylorSimplex::unit;

  static const univariate i_inv = univariate::i_inv;
  static const univariate i_pow2 = univariate::i_pow2;
  static const univariate i_matan = univariate::i_matan;
  static const univariate i_sqrt = univariate::i_sqrt;
  static const univariate i_acos = univariate::i_acos;
  static const univariate i_sin = univariate::i_sin;
  static const univariate i_asin = univariate::i_asin;

  static const interval sqrt3("1.7320508075688772935");
  static const interval sqrt2("1.4142135623730950488");
  static const interval quarter("0.25");
  static const interval half("0.5");
  static const interval two ("2");
  static const interval three ("3");
  static const interval four ("4");
  static const interval eight ("8");
  static const interval sixteen ("16");
  static const interval mone("-1");
  static const interval pi("3.1415926535897932385");
  static const interval const1 ("0.175479656091821810");
  static const interval sol0("0.5512855984325308079421");
  static const interval mm1("1.01208086842065466") ;
  static const interval mm2("0.0254145072695089280");


   };

/*implement ups_126*/
namespace local {
static int setAbsUps(const domain& x,const domain& z,double DD[6][6])
{
  double xa[6],za[6];
  for (int i=0;i<6;i++) {
    xa[i] = x.getValue(i);
    za[i] = z.getValue(i);
  }
  interval DDi[6][6];
  secondDerive::setU126(xa,za,DDi);
  intervalToAbsDouble(DDi,DD);
  return 1;
}
primitiveA upsPrimitive(linearization::ups_126,setAbsUps);
static const taylorFunction ups_126(&upsPrimitive);
};

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

/*implement ups_135*/
static primitiveC ups_135_Primitive
(&local::ups_126,
 &taylorSimplex::x1,&taylorSimplex::x3,&taylorSimplex::unit,
 &taylorSimplex::unit,&taylorSimplex::unit,&taylorSimplex::x5);
const taylorFunction ups_135(&::ups_135_Primitive);

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

/*implement acs_sqrt_x1_d4 */
const taylorFunction taylorSimplex::acs_sqrt_x1_d4 = 
  taylorFunction::uni_compose(univariate::i_acos,
			      taylorSimplex::y1 * local::quarter);

/*implement acs_sqrt_x2_d4 */
const taylorFunction taylorSimplex::acs_sqrt_x2_d4 = 
  taylorFunction::rotate2(taylorSimplex::acs_sqrt_x1_d4);


/*implement asn797 */
namespace local {
  //   `k * asn (cos (#0.797) * sin (pi / k))`;; 
  static const interval cos0797("0.69885563921392235500");
  static const taylorFunction sinpik =  uni(i_sin, uni(i_inv,x1) * pi);
  static const taylorFunction asn797k =  x1 * uni(i_asin,sinpik * cos0797);
}

const taylorFunction taylorSimplex::asn797k = local::asn797k;

/*implement asnFnhk */
// k * asn (( h * sqrt3 / #4.0 + sqrt(&1 - (h/ &2) pow 2)/ &2) * sin (pi/ k))`;;
// sinpik as above.
// x1 = h, x2 = k.
namespace local {
static const taylorFunction sinpiR2 = taylorFunction::rotate2(sinpik);
static const taylorFunction asnFh = 
  x1 * (sqrt3 / four) +
  (uni (i_sqrt,unit + 
  (uni (i_pow2,x1 * half)) * mone))*half;
static const taylorFunction asnFnhka = 
  uni(univariate::i_asin,asnFh * sinpiR2);
static const taylorFunction asnFnhk = x2 * asnFnhka;
}

const taylorFunction taylorSimplex::asnFnhk = local::asnFnhk;

/* implement lfun_y1 */
/*
`lfun_y1 (y1:real) (y2:real) (y3:real) 
  (y4:real) (y5:real) (y6:real) =  lfun y1`
`lfun h =  (h0 - h)/(h0 - &1)`
 */
namespace local {
  static const interval h0 ("1.26");
  static const taylorFunction lfun_y1 = 
    (unit * h0 + x1 * mone) * (one /  (h0 - one));


  static const taylorFunction lfun_sqrtx1_div2 = 
    (unit * h0 + y1 * mone * half) * (one / (h0 -one));

  const taylorFunction ldih_x = lfun_sqrtx1_div2 * dih;


};

const taylorFunction taylorSimplex::lfun_y1 = local::lfun_y1;


const taylorFunction taylorSimplex::ldih_x = local::ldih_x;
const taylorFunction taylorSimplex::ldih2_x = taylorFunction::rotate2 (local::ldih_x);
const taylorFunction taylorSimplex::ldih3_x = taylorFunction::rotate3 (local::ldih_x);
const taylorFunction taylorSimplex::ldih5_x = taylorFunction::rotate5 (local::ldih_x);
const taylorFunction taylorSimplex::ldih6_x = taylorFunction::rotate6 (local::ldih_x);

const taylorFunction taylorSimplex::lfun_sqrtx1_div2 = local::lfun_sqrtx1_div2;


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

namespace local { 
  static const taylorFunction x1square = x1  * x1;
}
const taylorFunction taylorSimplex::x1square = local::x1square;


/*implement arclength_x_123*/
//ArcCos[(x1 + x2 - x3)/(Sqrt[4 x1 x2])].

namespace local {
  static taylorFunction al_num = x1 + x2 + x3 * mone;
  static taylorFunction al_den = 
    uni(i_inv,uni(i_sqrt,(x1 * x2) * four));
  const taylorFunction arclength_x_123 = uni(i_acos,al_num * al_den);

 taylorFunction rotate234(const taylorFunction& f) {
  taylorFunction g = taylorFunction::compose
    (f,
     taylorSimplex::x2  , taylorSimplex::x3, taylorSimplex::x4,
     taylorSimplex::unit , taylorSimplex::unit, taylorSimplex::unit);
  return g;
 }

 taylorFunction rotate126(const taylorFunction& f) {
  taylorFunction g = taylorFunction::compose
    (f,
     taylorSimplex::x1  , taylorSimplex::x2, taylorSimplex::x6,
     taylorSimplex::unit , taylorSimplex::unit, taylorSimplex::unit);
  return g;
 }

 taylorFunction rotate345(const taylorFunction& f) {
  taylorFunction g = taylorFunction::compose
    (f,
     taylorSimplex::x3  , taylorSimplex::x4, taylorSimplex::x5,
     taylorSimplex::unit , taylorSimplex::unit, taylorSimplex::unit);
  return g;
 }


  const taylorFunction arclength_x_234 = rotate234(arclength_x_123);

  const taylorFunction arclength_x_126 = rotate126(arclength_x_123);

  const taylorFunction arclength_x_345 = rotate345(arclength_x_123);


};

const taylorFunction taylorSimplex::arclength_x_123 = local::arclength_x_123;

const taylorFunction taylorSimplex::arclength_x_234 = local::arclength_x_234;

const taylorFunction taylorSimplex::arclength_x_126 = local::arclength_x_126;

const taylorFunction taylorSimplex::arclength_x_345 = local::arclength_x_345;

/*
`sol_euler_x_div_sqrtdelta x1 x2 x3 x4 x5 x6 = 
  (let a = sqrt(x1*x2*x3) + sqrt( x1)*(x2 + x3 - x4)/ &2 + 
     sqrt(x2)*(x1 + x3 - x5)/ &2 + sqrt(x3)*(x1 + x2 - x6)/ &2 in
     (matan ((delta_x x1 x2 x3 x4 x5 x6)/(&4 * a pow 2 )))/( a))`;;
 */

/* implement sol_euler_x_div_sqrtdelta */  

namespace local {

  static const taylorFunction 
   a (y1 * y2 * y3 + y1 * (x2 + x3 + x4 * mone)* half +
     y2 * (x1 + x3 + x5* mone) * half + y3 * (x1 + x2 + x6* mone) * half);
  static const taylorFunction sol_euler_x_div_sqrtdelta = 
   (uni(i_matan, (delta * uni(i_inv,a * a * four ) )) * uni(i_inv,a));
};

const taylorFunction taylorSimplex::sol_euler_x_div_sqrtdelta = 
local::sol_euler_x_div_sqrtdelta;

const taylorFunction taylorSimplex::sol_euler246_x_div_sqrtdelta =
 taylorFunction::rotate4(taylorSimplex::sol_euler_x_div_sqrtdelta);

const taylorFunction taylorSimplex::sol_euler345_x_div_sqrtdelta = 
taylorFunction::rotate5(taylorSimplex::sol_euler_x_div_sqrtdelta);

const taylorFunction taylorSimplex::sol_euler156_x_div_sqrtdelta = 
taylorFunction::rotate6(taylorSimplex::sol_euler_x_div_sqrtdelta);

/*
 `dih_x_div_sqrtdelta_posbranch x1 x2 x3 x4 x5 x6 =
  ( let d_x4 = delta_x4 x1 x2 x3 x4 x5 x6 in
          let d = delta_x x1 x2 x3 x4 x5 x6 in
	     (sqrt(&4 * x1) / d_x4) * matan((&4 * x1 * d)/(d_x4 pow 2)))`;;
 */

namespace local {
  static const taylorFunction dih_x_div_sqrtdelta_posbranch =
    (y1 * uni(i_inv,delta_x4) * two) *
    uni(i_matan,(x1 * delta *  uni(i_inv,uni(i_pow2,delta_x4)) * four));
};

const taylorFunction taylorSimplex::dih_x_div_sqrtdelta_posbranch = 
  local::dih_x_div_sqrtdelta_posbranch;

const taylorFunction taylorSimplex::dih2_x_div_sqrtdelta_posbranch = 
  taylorFunction::rotate2 (taylorSimplex::dih_x_div_sqrtdelta_posbranch);

const taylorFunction taylorSimplex::dih3_x_div_sqrtdelta_posbranch = 
  taylorFunction::rotate3 (taylorSimplex::dih_x_div_sqrtdelta_posbranch);

const taylorFunction taylorSimplex::dih4_x_div_sqrtdelta_posbranch = 
  taylorFunction::rotate4 (taylorSimplex::dih_x_div_sqrtdelta_posbranch);

const taylorFunction taylorSimplex::dih5_x_div_sqrtdelta_posbranch = 
  taylorFunction::rotate5 (taylorSimplex::dih_x_div_sqrtdelta_posbranch);

const taylorFunction taylorSimplex::dih6_x_div_sqrtdelta_posbranch = 
  taylorFunction::rotate6 (taylorSimplex::dih_x_div_sqrtdelta_posbranch);



/*
`ldih_x_div_sqrtdelta_posbranch x1 x2 x3 x4 x5 x6 =
   lfun(sqrt(x1) / &2) * dih_x_div_sqrtdelta_posbranch x1 x2 x3 x4 x5 x6`;;

` !h. lfun h = (h0 - h) / (h0 - &1)`;;
 */

namespace local {
  static const taylorFunction ldih_x_div_sqrtdelta_posbranch =
    ( ( unit * h0 + y1 * (mone/ two)) * (one / (h0 - one))) * dih_x_div_sqrtdelta_posbranch;

  static const taylorFunction sqndelta = 
    uni(univariate::i_sqn,delta);

  static const taylorFunction ldih_x_n = sqndelta * ldih_x_div_sqrtdelta_posbranch;

}

const taylorFunction taylorSimplex::ldih_x_div_sqrtdelta_posbranch = 
  local::ldih_x_div_sqrtdelta_posbranch;

const taylorFunction taylorSimplex::ldih2_x_div_sqrtdelta_posbranch = 
  taylorFunction::rotate2 (taylorSimplex::ldih_x_div_sqrtdelta_posbranch);

const taylorFunction taylorSimplex::ldih3_x_div_sqrtdelta_posbranch = 
  taylorFunction::rotate3 (taylorSimplex::ldih_x_div_sqrtdelta_posbranch);

const taylorFunction taylorSimplex::ldih4_x_div_sqrtdelta_posbranch = 
  taylorFunction::rotate4 (taylorSimplex::ldih_x_div_sqrtdelta_posbranch);

const taylorFunction taylorSimplex::ldih5_x_div_sqrtdelta_posbranch = 
  taylorFunction::rotate5 (taylorSimplex::ldih_x_div_sqrtdelta_posbranch);

const taylorFunction taylorSimplex::ldih6_x_div_sqrtdelta_posbranch = 
  taylorFunction::rotate6 (taylorSimplex::ldih_x_div_sqrtdelta_posbranch);


/*
 `taum_y1 a b y1 (y2) (y3) (y4) (y5) (y6) = 
  taum (&2) (&2) (&2) a b y1`;;

 `taum_y2 a b (y1) (y2) (y3) (y4) (y5) (y6) = 
  taum (&2) (&2) (&2) a b y2`;;

 `taum_y1_y2 a (y1) (y2) (y3) (y4) (y5) (y6) = 
  taum (&2) (&2) (&2) a y1 y2`;;

`taum_x1 a b x1 x2 x3 x4 x5 x6 = 
  taum_y1 a b (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)`;;

`taum_x2 a b x1 x2 x3 x4 x5 x6 = 
  taum_y2 a b (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)`;;

`taum_x1_x2 a x1 x2 x3 x4 x5 x6 = 
  taum_y1_y2 a (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)`;;

`taum y1 y2 y3 y4 y5 y6 = rhazim y1 y2 y3 y4 y5 y6 + rhazim2 y1 y2 y3 y4 y5 y6 + rhazim3 y1  y2 y3 y4 y5 y6 - (&1 + const1)* pi`

 `arclength_y1 a b (y1) (y2) (y3) (y4) (y5) (y6) =  arclength y1 a b`;;

 `arclength_x1 a b x1 x2 x3 x4 x5 x6 = 
  arclength_y1 a b (sqrt x1) (sqrt x2) (sqrt x3) (sqrt x4) (sqrt x5) (sqrt x6)`;;
 */

namespace local {



  static const taylorFunction taum = 
    taylorSimplex::rhazim + taylorSimplex::rhazim2 +taylorSimplex::rhazim3
    + unit * (pi * mone * (one + const1));

  static const taylorFunction taum_x1(const interval& a,const interval& b)
  {
    taylorFunction g = taylorFunction::compose
      (taum,
       unit * four  , unit * four, unit * four,
       unit * (a * a) , unit * (b * b) , x1);
    return g;
  }

  static const taylorFunction taum_x2(const interval& a,const interval& b)
  {
    taylorFunction g = taylorFunction::compose
      (taum,
       unit * four  , unit * four, unit * four,
       unit * (a * a) , unit * (b * b) , x2);
    return g;
  }

  static const taylorFunction taum_x1_x2(const interval& a)
  {
    taylorFunction g = taylorFunction::compose
      (taum,
       unit * four, unit * four, unit * four,
       unit * (a * a) , x1 , x2);
    return g;
  }

  static const taylorFunction arclength_x1
   (const interval& b,const interval& c) {
    taylorFunction g = taylorFunction::compose
    (taylorSimplex::arclength_x_123,
     x1, unit * (b * b), unit * (c* c), unit,unit,unit);
    return g;
  }

  static const taylorFunction arclength_x2
   (const interval& b,const interval& c) {
    taylorFunction g = taylorFunction::compose
    (taylorSimplex::arclength_x_123,
     x2, unit * (b * b), unit * (c* c), unit,unit,unit);
    return g;
  }


  static const taylorFunction surfR126d
  (const interval& ic2) {
    taylorFunction c2 = unit * (ic2);
    taylorFunction g = 
      ((x2 + x6 + x1* mone) * y1 + (x1 + x6 + x2 * mone) * y2) * uni(i_inv,local::ups_126) * 
      uni(i_sqrt,taylorFunction::compose
	  (delta,x1,x2,c2,c2,c2,x6)) * quarter;
      return g;
  };

  taylorFunction surfR12_6rad_x =  // cf. S.P.I Sec. 8.6.3.
      ((x2 + x6 + x1* mone) * y1 + (x1 + x6 + x2 * mone) * y2) * chi126 *
      uni(i_inv,
	  local::ups_126 * uni(i_sqrt,delta) * eight);

  static const taylorFunction surf_x =     local::surfR12_6rad_x +
    taylorFunction::rotate2 (local::surfR12_6rad_x) +
    taylorFunction::rotate3 (local::surfR12_6rad_x);
};

const taylorFunction taylorSimplex::surfR126d  (const interval& circumrad)  {
  return local::surfR126d(circumrad);
}

const taylorFunction taylorSimplex::surf_x = local::surf_x;

const taylorFunction 
 taylorSimplex::taum_x1(const interval& a,const interval& b) {
  return local::taum_x1(a,b);
}

const taylorFunction 
 taylorSimplex::taum_x2(const interval& a,const interval& b) {
  return local::taum_x2(a,b);
} 

const taylorFunction 
 taylorSimplex::taum_x1_x2(const interval& a) {
  return local::taum_x1_x2(a);
}  

const taylorFunction 
taylorSimplex::arclength_x1(const interval& b,const interval& c) {
  return local::arclength_x1(b,c);
}

const taylorFunction 
taylorSimplex::arclength_x2(const interval& b,const interval& c) {
  return local::arclength_x2(b,c);
}  

namespace local {

  /* `!x1 x2 x3 x4 x5 x6.  
  &0 <= x1 /\ &0 <= x2 /\ &0 <= x6 ==>
  (vol3_x_sqrt x1 x2 x3 x4 x5 x6 = vol_x x1 x2 (&2) (&2) (&2) x6)`, */

  static const taylorFunction two_unit = unit * two;

  static const taylorFunction vol3_x_sqrt = 
    taylorFunction::compose(taylorSimplex::vol_x,
			    x1,x2,two_unit,two_unit,two_unit,x6);

  static const taylorFunction vol3_x_135_s2 = 
    taylorFunction::compose(taylorSimplex::vol_x,
			    x1,two_unit,x3,two_unit,x5,two_unit);



  /*
`!x1 x2 x3 x4 x5 x6.  
   &0 <= x1 /\ &0 <= x2 /\ &0 <= x6 ==>
   vol3f_x_lfun x1 x2 x3 x4 x5 x6 =   (&2 * mm1 / pi) *
             (&2 * dih_x x1 x2 (&2) (&2) (&2) x6 +
              &2 * dih2_x x1 x2 (&2) (&2) (&2) x6 +
              &2 * dih6_x x1 x2 (&2) (&2) (&2) x6 +
              dih3_x x1 x2 (&2) (&2) (&2) x6 +
              dih4_x x1 x2 (&2) (&2) (&2) x6 +
              dih5_x x1 x2 (&2) (&2) (&2) x6 - &3 * pi) -
             (&8 * mm2 / pi) *
             ( ldih_x x1 x2 (&2) (&2) (&2) x6 +
              ldih2_x x1 x2 (&2) (&2) (&2) x6 +
              ldih6_x x1 x2 (&2) (&2) (&2) x6)`,
   */


  static const taylorFunction vol3f_x_lfun_mm1 = 
    taylorFunction::compose(taylorSimplex::dih,x1,x2,two_unit,two_unit,two_unit,x6) * two+
    taylorFunction::compose(taylorSimplex::dih2,x1,x2,two_unit,two_unit,two_unit,x6) * two+
    taylorFunction::compose(taylorSimplex::dih6,x1,x2,two_unit,two_unit,two_unit,x6) * two+
    taylorFunction::compose(taylorSimplex::dih3,x1,x2,two_unit,two_unit,two_unit,x6) +
    taylorFunction::compose(taylorSimplex::dih4,x1,x2,two_unit,two_unit,two_unit,x6) +
    taylorFunction::compose(taylorSimplex::dih5,x1,x2,two_unit,two_unit,two_unit,x6) +
    unit * (pi * mone * three);
 
   static const taylorFunction vol3f_x_lfun_mm2 = 
     taylorFunction::compose(taylorSimplex::ldih_x,x1,x2,two_unit,two_unit,two_unit,x6) +
     taylorFunction::compose(taylorSimplex::ldih2_x,x1,x2,two_unit,two_unit,two_unit,x6) +
     taylorFunction::compose(taylorSimplex::ldih6_x,x1,x2,two_unit,two_unit,two_unit,x6);

  static const taylorFunction vol3f_x_lfun = 
    vol3f_x_lfun_mm1 * (two * mm1 / pi) + vol3f_x_lfun_mm2 * (eight * mone * mm2 /pi);

  /*
  `!x1 x2 x3 x4 x5 x6.  
   ((&2 * h0) pow 2 <= x1) /\ &0 <= x2 /\ &0 <= x6 ==>
   vol3f_x_sqrt2_lmplus x1 x2 x3 x4 x5 x6 =   (&2 * mm1 / pi) *
             (&2 * dih_x x1 x2 (&2) (&2) (&2) x6 +
              &2 * dih2_x x1 x2 (&2) (&2) (&2) x6 +
              &2 * dih6_x x1 x2 (&2) (&2) (&2) x6 +
              dih3_x x1 x2 (&2) (&2) (&2) x6 +
              dih4_x x1 x2 (&2) (&2) (&2) x6 +
              dih5_x x1 x2 (&2) (&2) (&2) x6 - &3 * pi) -
             (&8 * mm2 / pi) *
             (
              ldih2_x x1 x2 (&2) (&2) (&2) x6 +
              ldih6_x x1 x2 (&2) (&2) (&2) x6)`,
  */

  static taylorFunction mk_135 (const taylorFunction& f) {
    return taylorFunction::compose(f,x1,two_unit,x3,two_unit,x5,two_unit);
  }

  static taylorFunction mk_126 (const taylorFunction& f) {
    return taylorFunction::compose(f,x1,x2,two_unit,two_unit,two_unit,x6);
  }

  const taylorFunction ldih_x_126_n = mk_126 (ldih_x_n);
  const taylorFunction ldih_x_135_n = mk_135 (ldih_x_n);


  static const taylorFunction vol3f_x_lfun_mm2_no_dih1 = 
    mk_126(taylorSimplex::ldih2_x) + mk_126(taylorSimplex::ldih6_x);

  /*
  static const taylorFunction vol3f_x_lfun_mm2_no_dih1 = 
      taylorFunction::compose(taylorSimplex::ldih2_x,x1,x2,two_unit,two_unit,two_unit,x6) +
     taylorFunction::compose(taylorSimplex::ldih6_x,x1,x2,two_unit,two_unit,two_unit,x6);
  */

  static const taylorFunction vol3f_x_sqrt2_lmplus = 
    vol3f_x_lfun_mm1 * (two * mm1 / pi) + vol3f_x_lfun_mm2_no_dih1 * (eight * mone * mm2 /pi);



  static const taylorFunction vol2r = (two_unit  + x1 * (mone/four) ) * (two * pi/three);

  static const taylorFunction vv_term_m1 = 
    (unit + y1 * (mone / (two * sqrt2))) * (four * mm1 ) ;

  static const taylorFunction vv_term_m2 = 
    lfun_sqrtx1_div2 * sixteen * mm2;

static const taylorFunction dih_x_126_s2 = mk_126(taylorSimplex::dih);
static const taylorFunction dih_x_135_s2 = mk_135(taylorSimplex::dih);


  // implement upper_dih
  /*
  `upper_dih_x x1 x2 x3 x4 x5 x6 =
  (let d = delta_x x1 x2 x3 x4 x5 x6 in
  let d4 = delta_x4 x1 x2 x3 x4 x5 x6 in (
   &2 * sqrt x1 * sqp d *
    matan (&4 * x1 * d / (d4 pow 2) ) / d4))`;;
   */
  static const taylorFunction rdelta_x4 = uni(univariate::i_inv,delta_x4);

  static const  taylorFunction upper_dih = 
    (y1 * uni (univariate::i_sqp,delta) * rdelta_x4 *
    uni(univariate::i_matan, ( x1 * delta * uni(univariate::i_pow2, rdelta_x4) ) * four) ) * two;


  static const taylorFunction upper_dih_x_126 = mk_126(upper_dih);
  static const taylorFunction upper_dih_x_135 = mk_135(upper_dih);


  // gamma3f_vLR_lfun
    static const taylorFunction gamma3f_x_vLR_lfun = 
    (dih + dih_x_126_s2 * mone +  dih_x_135_s2 * mone) * 
       (vol2r + vv_term_m1 * mone + vv_term_m2 ) *     (one / (two * pi));

  // gamma3f_vLR0
    static const taylorFunction gamma3f_x_vLR0 = 
    (dih + dih_x_126_s2 * mone +  dih_x_135_s2 * mone) * 
       (vol2r + vv_term_m1 * mone  ) *     (one / (two * pi));

  static const interval m03("-0.03");



  // gamma3f_x_vL_lfun
    static const taylorFunction gamma3f_x_vL_lfun = 
    (dih + dih_x_126_s2 * mone + unit * m03) * 
       (vol2r + vv_term_m1 * mone + vv_term_m2 ) *     (one / (two * pi));

  // gamma3f_vL0
    static const taylorFunction gamma3f_x_vL0 = 
    (dih + dih_x_126_s2 * mone +  unit * m03) * 
       (vol2r + vv_term_m1 * mone  ) *     (one / (two * pi));

  // gamma3f_v_lfun
    static const taylorFunction gamma3f_x_v_lfun = 
    (dih +  unit * two * m03) * 
       (vol2r + vv_term_m1 * mone + vv_term_m2 ) *     (one / (two * pi));

  // gamma3f_v0
    static const taylorFunction gamma3f_x_v0 = 
    (dih +   unit * two * m03) * 
       (vol2r + vv_term_m1 * mone  ) *     (one / (two * pi));

  // gamma3f_vLR_x_nlfun
    static const taylorFunction gamma3f_vLR_x_nlfun = 
    (dih + upper_dih_x_126 * mone + upper_dih_x_135 * mone) * 
       (vol2r + vv_term_m1 * mone + vv_term_m2 ) *     (one / (two * pi));

  // gamma3f_vLR_x_n0
    static const taylorFunction gamma3f_vLR_x_n0 = 
    (dih + upper_dih_x_126 * mone + upper_dih_x_135 * mone) * 
       (vol2r + vv_term_m1 * mone  ) *     (one / (two * pi));

  // gamma3f_vL_x_nlfun
    static const taylorFunction gamma3f_vL_x_nlfun = 
    (dih + upper_dih_x_126 * mone + unit * m03) * 
       (vol2r + vv_term_m1 * mone + vv_term_m2 ) *     (one / (two * pi));

  // gamma3f_vL_x_n0
    static const taylorFunction gamma3f_vL_x_n0 = 
    (dih + upper_dih_x_126 * mone +  unit * m03) * 
       (vol2r + vv_term_m1 * mone  ) *     (one / (two * pi));

  // gamma3f_135_x_s_n
  static const taylorFunction gamma3f_135_x_s_n =
    sqndelta * (unit * (one/twelve) + (sol_euler_x_div_sqrtdelta + taylorSimplex::sol_euler156_x_div_sqrtdelta + taylorSimplex::sol_euler345_x_div_sqrtdelta) * (mone * two * mm1 / pi));

 // gamma3f_126_x_s_n
  static const taylorFunction gamma3f_126_x_s_n =
    sqndelta * (unit * (one/twelve) + (sol_euler_x_div_sqrtdelta + taylorSimplex::sol_euler246_x_div_sqrtdelta + taylorSimplex::sol_euler156_x_div_sqrtdelta) * (mone* two * mm1 / pi));


  

  // num1
  /* thm =  |- !x1 x2 x3 x4 x5 x6.         num1 x1 x2 x3 x4 x5 x6 =
         &64 * x1 * x4 -          &32 * x2 * x4 -         &32 * x3 * x4 -
         &4 * x1 * x4 pow 2 -          &32 * x2 * x5 +         &32 * x3 * x5 +
         &4 * x2 * x4 * x5 +         &32 * x2 * x6 - &32 * x3 * x6 +         &4 * x3 * x4 * x6 */
  static const interval t64("64");
  static const interval t32("32");
  static const taylorFunction num1 = 
     x1 * x4 * t64 +  x2 * x4 *mone * t32 +  x3 * x4 *mone * t32 
    + x1 * x4 * x4 * mone * four  +  x2 * x5 * mone * t32 + x3 * x5 * t32
    + x2 * x4 * x5  * four +  x2 * x6 * t32 + x3 * x6 * mone * t32 +  x3 * x4 * x6 * four;

  static const taylorFunction operator*(const taylorFunction& t,int j) {
    return t * interval(j * 1.0, j * 1.0);
  }

  static const taylorFunction operator*(int j,const taylorFunction& t) {
    return t * interval(j * 1.0, j * 1.0);
  }


  static const taylorFunction operator-(const taylorFunction& u,const taylorFunction& t) {
    return u + t * mone;
  }


  // implement edge_flat2_x.
  const taylorFunction bx_neg_quadratic = x1*(x2 + x3 + x5 + x6) -x1 * x1 - (x3 - x5)*(x2 - x6) ;
  const taylorFunction disc_quadratic =  uni(i_sqrt, ups_126 * ups_135 );
  const taylorFunction ax2_inv_quadratic = uni(i_inv,x1 * two) ;
  const taylorFunction edge_flat2_x = (bx_neg_quadratic + disc_quadratic) * ax2_inv_quadratic;

  // implement taum_x.
  /* |- !x1 x2 x3 x4 x5 x6.
         taum_x x1 x2 x3 x4 x5 x6 =
         rhazim_x x1 x2 x3 x4 x5 x6 +
         rhazim2_x x1 x2 x3 x4 x5 x6 +
         rhazim3_x x1 x2 x3 x4 x5 x6 - (&1 + const1) * pi
  */
  const taylorFunction taum_x = taylorSimplex::rhazim + taylorSimplex::rhazim2 + 
    taylorSimplex::rhazim3 - unit  * pi * (one + const1);

  // implement flat_term_x.
  const taylorFunction flat_term_x = (y1 - unit * two * h0) * sol0 * (one / (two * h0 - two));

  // implement dih_template_B_x.
  /*
    dih_template_B_x x15 x45 x34 x12 x25 x1 x2 x3 x4 x5 x6 =
         dih_x x1 x2 x5 x25 x15 x12 -
         dih_x x1 x3 x4 x34 (edge_flat2_x x5 x1 x4 (&0) x45 x15)
         (edge_flat2_x x2 x1 x3 (&0) x12 x12)
   */
  const taylorFunction dih_template_B_x(const interval& x15,const interval& x45,
					const interval& x34,const interval& x12, 
					const interval& x25)
  {
    static const interval zero ("0");
    taylorFunction uz = unit * zero;
    taylorFunction ef_514 = taylorFunction::compose(
						    edge_flat2_x,x5,x1,x4,uz,unit * x45, unit * x15);
    taylorFunction ef_213 = taylorFunction::compose(
						    edge_flat2_x,x2,x1,x3,uz, unit * x12, unit * x12);
    taylorFunction d_125 = taylorFunction::compose(dih,
						    x1,x2,x5,unit * x25, unit * x15, unit * x12);
    taylorFunction d_134 = taylorFunction::compose(dih,
						   x1,x3,x4,unit * x34,ef_514,ef_213);
    taylorFunction d = d_125 - d_134;
    return d;
  };

  // implement delta_template_B_x.
  /*
    delta_template_B_x x15 x45 x34 x12 x1 x2 x3 x4 x5 x6 =
         delta_x x1 x3 x4 x34 (edge_flat2_x x5 x1 x4 (&0) x45 x15)
         (edge_flat2_x x2 x1 x3 (&0) x12 x12)
   */
  const taylorFunction delta_template_B_x(const interval& x15,const interval& x45,
					const interval& x34,const interval& x12)
  {
    static const interval zero ("0");
    taylorFunction uz = unit * zero;
    taylorFunction ef_514 = taylorFunction::compose(
						    edge_flat2_x,x5,x1,x4,uz,unit * x45, unit * x15);
    taylorFunction ef_213 = taylorFunction::compose(
						    edge_flat2_x,x2,x1,x3,uz, unit * x12, unit * x12);
    taylorFunction d_134 = taylorFunction::compose(delta,
						   x1,x3,x4,unit * x34,ef_514,ef_213);
    return d_134;
  };



  // implement taum_template_B_x.
  /*
     taum_template_B_x x15 x45 x34 x12 x1 x2 x3 x4 x5 x6 =
         taum_x x1 x3 x4 x34 (edge_flat2_x x5 x1 x4 (&0) x45 x15)
         (edge_flat2_x x2 x1 x3 (&0) x12 x12) +
         flat_term_x x2 +
         flat_term_x x5
   */
  const taylorFunction taum_template_B_x(const interval& x15,const interval& x45,
					 const interval& x34,const interval& x12)
  {
    static const interval zero ("0");
   taylorFunction uz = unit * zero;
    taylorFunction ef_514 = taylorFunction::compose(
						    edge_flat2_x,x5,x1,x4,uz,unit * x45, unit * x15);
    taylorFunction ef_213 = taylorFunction::compose(
						    edge_flat2_x,x2,x1,x3,uz, unit * x12, unit * x12);
    taylorFunction t_134 = taylorFunction::compose(taum_x,
						   x1,x3,x4,unit * x34,ef_514,ef_213);
    taylorFunction ft_2 = taylorFunction::rotate2(flat_term_x);
    taylorFunction ft_5 = taylorFunction::rotate5(flat_term_x);
    return (t_134 + ft_2 + ft_5);
  };

  // implement dih_hexall_x.
  /*
`dih_hexall_x x14 x12 x23 x1 x2 x3 x4 x5 (x6:real) = 
   dih_x x1 x2 x4 ((&2 * h0) pow 2) x14 x12 - 
   dih_x x1 x3 x4 x5 x14 (edge_flat2_x x2 x1 x3 (&0) x23 x12)`;;
   */
  static const taylorFunction c4h0s = unit * (h0 * h0 * four);

  const taylorFunction dih_hexall_x(const interval& x14, const interval& x12,
						   const interval & x23) {
    static const interval zero("0");
    taylorFunction uz = unit * zero;
    taylorFunction ef_213 = taylorFunction::compose(edge_flat2_x,x2,x1,x3,uz,unit * x23, unit * x12);
    taylorFunction d1 = taylorFunction::compose(dih,x1,x2,x4,c4h0s,unit * x14, unit * x12);
    taylorFunction d2 = taylorFunction::compose(dih,x1,x3,x4,x5,unit * x14, ef_213);
    return d1 + d2 * mone;
  }

  // implement taum_hexall_x.
  /*
  `taum_hexall_x  x14 x12 x23  x1 x2 x3 x4 x5 (x6:real) = 
   taum_x x1 x3 x4 x5 x14 (edge_flat2_x x2 x1 x3 (&0) x23 x12) + flat_term_x x2`;;
   */
  const taylorFunction taum_hexall_x(const interval& x14, const interval& x12,
						    const interval & x23) {
    static const interval zero("0");
    taylorFunction uz = unit * zero;
    taylorFunction ef_213 = taylorFunction::compose(edge_flat2_x,x2,x1,x3,uz,unit * x23, unit * x12);
    taylorFunction t1 = taylorFunction::compose(taum_x,x1,x3,x4,x5,unit * x14,ef_213);
    taylorFunction t2 = taylorFunction::rotate2(flat_term_x);
    return t1 + t2;
  }



const taylorFunction monomial(int i1,int i2,int i3,int i4,int i5,int i6) {
  return taylorSimplex::monomial(i1, i2,i3,i4,i5,i6);
}

  // num_combo1 = ((num1^2 - 1/100 num2 // Simplify) /. {e1 -> x1, e2 -> x2, 
  //          e3 -> x3, a2 -> x4, b2 -> x5, c2 -> x6}) // CForm;
  static const taylorFunction x4_pow2 = x4 * x4;
  static const taylorFunction x5_pow2 = x5 * x5;
  static const taylorFunction x6_pow2 = x6 * x6;
  static const taylorFunction x4_pow3 = x4_pow2 * x4;
  static const taylorFunction x4_pow4 = x4_pow2 * x4_pow2;
  static const taylorFunction x4_pow5 = x4_pow3 * x4_pow2;
  static const taylorFunction x5mx6 = (x5 + x6 * mone);
  static const taylorFunction x5mx6_pow3 = x5mx6 * x5mx6 * x5mx6;
  static const taylorFunction num_combo1_subexp =
    x1* x4_pow2  + x4*(x1*16 + x2*(unit*-8 + x5) + 
    x3*(unit*-8 + x6))*mone + (x2 + x3*mone)*(x5 + x6*mone)*8;
  static const interval t25("25");

  // slow: 10^6 cases took 1292075074 -- 1292077520.
  // This is about 11x slower than num_combo1_alt.
  // deprecated.
  static const taylorFunction num_combo1_deprecated = 
     (2*(-2*x1*x4_pow5 + 2* x4_pow4 *(32*x1 + 3*(x2*(unit*-8 + x5) + x3*(unit*-8 + x6))) + 
       200*num_combo1_subexp * num_combo1_subexp  + 256*(x2 + x3*mone)* x5mx6_pow3  + 
       2* x4_pow2 *(x5 - x6)*(384*(x2 + x3*mone) + x2* x5_pow2  + 
          x5*(x1*-32 + x2*(unit*56  + 9*x6*mone) + 9*x3*(unit*-8 + x6)) + 8*(4*x1 + 9*x2 + x3*-7)*x6 
     +           x3* x6_pow2*mone ) - 16*x4*(x5 - x6)*
        ((x2 - 3*x3)* x5_pow2  + x6*(32*x1 + 3*x2*(unit*16 + x6) - x3*(unit*80 + x6)) - 
          4*x5*(8*x1 - 3*x3*(unit*-4 + x6) + x2*(unit*-20 + 3*x6))) + 
        x4_pow3 *(2*x1*(unit*-256 +  x5_pow2  - 2*x5*x6 +  x6_pow2 ) + 
          x2*( x5_pow2 *(unit*-8 + x6) - 16*x5*(unit*3 + x6) + 16*(unit*16 + 9*x6)) + 
		  x3*(x5*(unit*144 - 16*x6 +  x6_pow2 ) - 8*(unit*-32 + 6*x6 +  x6_pow2 ))))) * (one/t25);

static const taylorFunction num_combo1_alt = 
(512*monomial(0,0,1,0,0,3) - 1536*monomial(0,0,1,0,1,2) + 1536*monomial(0,0,1,0,2,1) - 
   512*monomial(0,0,1,0,3,0) - 2560*monomial(0,0,1,1,0,2) - 32*monomial(0,0,1,1,0,3) + 
   1024*monomial(0,0,1,1,1,1) + 416*monomial(0,0,1,1,1,2) + 1536*monomial(0,0,1,1,2,0) - 
   480*monomial(0,0,1,1,2,1) + 96*monomial(0,0,1,1,3,0) + 1536*monomial(0,0,1,2,0,1) + 
   224*monomial(0,0,1,2,0,2) + 4*monomial(0,0,1,2,0,3) - 1536*monomial(0,0,1,2,1,0) + 
   64*monomial(0,0,1,2,1,1) - 40*monomial(0,0,1,2,1,2) - 288*monomial(0,0,1,2,2,0) + 
   36*monomial(0,0,1,2,2,1) + 512*monomial(0,0,1,3,0,0) - 96*monomial(0,0,1,3,0,1) - 
   16*monomial(0,0,1,3,0,2) + 288*monomial(0,0,1,3,1,0) - 32*monomial(0,0,1,3,1,1) + 
   2*monomial(0,0,1,3,1,2) - 96*monomial(0,0,1,4,0,0) + 12*monomial(0,0,1,4,0,1) + 
   25600*monomial(0,0,2,0,0,2) - 51200*monomial(0,0,2,0,1,1) + 25600*monomial(0,0,2,0,2,0) + 
   51200*monomial(0,0,2,1,0,1) - 6400*monomial(0,0,2,1,0,2) - 51200*monomial(0,0,2,1,1,0) + 
   6400*monomial(0,0,2,1,1,1) + 25600*monomial(0,0,2,2,0,0) - 6400*monomial(0,0,2,2,0,1) + 
   400*monomial(0,0,2,2,0,2) - 512*monomial(0,1,0,0,0,3) + 1536*monomial(0,1,0,0,1,2) - 
   1536*monomial(0,1,0,0,2,1) + 512*monomial(0,1,0,0,3,0) + 1536*monomial(0,1,0,1,0,2) + 
   96*monomial(0,1,0,1,0,3) + 1024*monomial(0,1,0,1,1,1) - 480*monomial(0,1,0,1,1,2) - 
   2560*monomial(0,1,0,1,2,0) + 416*monomial(0,1,0,1,2,1) - 32*monomial(0,1,0,1,3,0) - 
   1536*monomial(0,1,0,2,0,1) - 288*monomial(0,1,0,2,0,2) + 1536*monomial(0,1,0,2,1,0) + 
   64*monomial(0,1,0,2,1,1) + 36*monomial(0,1,0,2,1,2) + 224*monomial(0,1,0,2,2,0) - 
   40*monomial(0,1,0,2,2,1) + 4*monomial(0,1,0,2,3,0) + 512*monomial(0,1,0,3,0,0) + 
   288*monomial(0,1,0,3,0,1) - 96*monomial(0,1,0,3,1,0) - 32*monomial(0,1,0,3,1,1) - 
   16*monomial(0,1,0,3,2,0) + 2*monomial(0,1,0,3,2,1) - 96*monomial(0,1,0,4,0,0) + 
   12*monomial(0,1,0,4,1,0) - 51200*monomial(0,1,1,0,0,2) + 102400*monomial(0,1,1,0,1,1) - 
   51200*monomial(0,1,1,0,2,0) + 6400*monomial(0,1,1,1,0,2) - 12800*monomial(0,1,1,1,1,1) + 
   6400*monomial(0,1,1,1,2,0) + 51200*monomial(0,1,1,2,0,0) - 6400*monomial(0,1,1,2,0,1) - 
   6400*monomial(0,1,1,2,1,0) + 800*monomial(0,1,1,2,1,1) + 25600*monomial(0,2,0,0,0,2) - 
   51200*monomial(0,2,0,0,1,1) + 25600*monomial(0,2,0,0,2,0) - 51200*monomial(0,2,0,1,0,1) + 
   51200*monomial(0,2,0,1,1,0) + 6400*monomial(0,2,0,1,1,1) - 6400*monomial(0,2,0,1,2,0) + 
   25600*monomial(0,2,0,2,0,0) - 6400*monomial(0,2,0,2,1,0) + 400*monomial(0,2,0,2,2,0) + 
   1024*monomial(1,0,0,1,0,2) - 2048*monomial(1,0,0,1,1,1) + 1024*monomial(1,0,0,1,2,0) - 
   128*monomial(1,0,0,2,0,2) + 256*monomial(1,0,0,2,1,1) - 128*monomial(1,0,0,2,2,0) - 
   1024*monomial(1,0,0,3,0,0) + 4*monomial(1,0,0,3,0,2) - 8*monomial(1,0,0,3,1,1) + 
   4*monomial(1,0,0,3,2,0) + 128*monomial(1,0,0,4,0,0) - 4*monomial(1,0,0,5,0,0) - 
   102400*monomial(1,0,1,1,0,1) + 102400*monomial(1,0,1,1,1,0) - 
   102400*monomial(1,0,1,2,0,0) + 19200*monomial(1,0,1,2,0,1) - 6400*monomial(1,0,1,2,1,0) + 
   6400*monomial(1,0,1,3,0,0) - 800*monomial(1,0,1,3,0,1) + 102400*monomial(1,1,0,1,0,1) - 
   102400*monomial(1,1,0,1,1,0) - 102400*monomial(1,1,0,2,0,0) - 6400*monomial(1,1,0,2,0,1) + 
   19200*monomial(1,1,0,2,1,0) + 6400*monomial(1,1,0,3,0,0) - 800*monomial(1,1,0,3,1,0) + 
   102400*monomial(2,0,0,2,0,0) - 12800*monomial(2,0,0,3,0,0) + 400*monomial(2,0,0,4,0,0))*(one/t25);

static const taylorFunction num2 = 
  (-2048)*monomial(0,0,1,0,0,3) + 6144*monomial(0,0,1,0,1,2) - 6144*monomial(0,0,1,0,2,1) + 
   2048*monomial(0,0,1,0,3,0) + 10240*monomial(0,0,1,1,0,2) + 128*monomial(0,0,1,1,0,3) - 
   4096*monomial(0,0,1,1,1,1) - 1664*monomial(0,0,1,1,1,2) - 6144*monomial(0,0,1,1,2,0) + 
   1920*monomial(0,0,1,1,2,1) - 384*monomial(0,0,1,1,3,0) - 6144*monomial(0,0,1,2,0,1) - 
   896*monomial(0,0,1,2,0,2) - 16*monomial(0,0,1,2,0,3) + 6144*monomial(0,0,1,2,1,0) - 
   256*monomial(0,0,1,2,1,1) + 160*monomial(0,0,1,2,1,2) + 1152*monomial(0,0,1,2,2,0) - 
   144*monomial(0,0,1,2,2,1) - 2048*monomial(0,0,1,3,0,0) + 384*monomial(0,0,1,3,0,1) + 
   64*monomial(0,0,1,3,0,2) - 1152*monomial(0,0,1,3,1,0) + 128*monomial(0,0,1,3,1,1) - 
   8*monomial(0,0,1,3,1,2) + 384*monomial(0,0,1,4,0,0) - 48*monomial(0,0,1,4,0,1) + 
   2048*monomial(0,1,0,0,0,3) - 6144*monomial(0,1,0,0,1,2) + 6144*monomial(0,1,0,0,2,1) - 
   2048*monomial(0,1,0,0,3,0) - 6144*monomial(0,1,0,1,0,2) - 384*monomial(0,1,0,1,0,3) - 
   4096*monomial(0,1,0,1,1,1) + 1920*monomial(0,1,0,1,1,2) + 10240*monomial(0,1,0,1,2,0) - 
   1664*monomial(0,1,0,1,2,1) + 128*monomial(0,1,0,1,3,0) + 6144*monomial(0,1,0,2,0,1) + 
   1152*monomial(0,1,0,2,0,2) - 6144*monomial(0,1,0,2,1,0) - 256*monomial(0,1,0,2,1,1) - 
   144*monomial(0,1,0,2,1,2) - 896*monomial(0,1,0,2,2,0) + 160*monomial(0,1,0,2,2,1) - 
   16*monomial(0,1,0,2,3,0) - 2048*monomial(0,1,0,3,0,0) - 1152*monomial(0,1,0,3,0,1) + 
   384*monomial(0,1,0,3,1,0) + 128*monomial(0,1,0,3,1,1) + 64*monomial(0,1,0,3,2,0) - 
   8*monomial(0,1,0,3,2,1) + 384*monomial(0,1,0,4,0,0) - 48*monomial(0,1,0,4,1,0) - 
   4096*monomial(1,0,0,1,0,2) + 8192*monomial(1,0,0,1,1,1) - 4096*monomial(1,0,0,1,2,0) + 
   512*monomial(1,0,0,2,0,2) - 1024*monomial(1,0,0,2,1,1) + 512*monomial(1,0,0,2,2,0) + 
   4096*monomial(1,0,0,3,0,0) - 16*monomial(1,0,0,3,0,2) + 32*monomial(1,0,0,3,1,1) - 
16*monomial(1,0,0,3,2,0) - 512*monomial(1,0,0,4,0,0) + 16*monomial(1,0,0,5,0,0);

}; // end local scope


const taylorFunction taylorSimplex::vol3_x_sqrt = local::vol3_x_sqrt;

const taylorFunction taylorSimplex::vol3_x_135_s2 = local::vol3_x_135_s2;

const taylorFunction taylorSimplex::vol3f_x_lfun = local::vol3f_x_lfun;

const taylorFunction taylorSimplex::vol3f_x_sqrt2_lmplus = local::vol3f_x_sqrt2_lmplus;

const taylorFunction taylorSimplex::dih_x_126_s2 = local::dih_x_126_s2;
const taylorFunction taylorSimplex::dih2_x_126_s2 = local::mk_126(taylorSimplex::dih2);
const taylorFunction taylorSimplex::dih3_x_126_s2 = local::mk_126(taylorSimplex::dih3);
const taylorFunction taylorSimplex::dih4_x_126_s2 = local::mk_126(taylorSimplex::dih4);
const taylorFunction taylorSimplex::dih5_x_126_s2 = local::mk_126(taylorSimplex::dih5);
const taylorFunction taylorSimplex::dih6_x_126_s2 = local::mk_126(taylorSimplex::dih6);
 
const taylorFunction taylorSimplex::ldih_x_126_s2 = local::mk_126(taylorSimplex::ldih_x);
const taylorFunction taylorSimplex::ldih2_x_126_s2 = local::mk_126(taylorSimplex::ldih2_x);
const taylorFunction taylorSimplex::ldih6_x_126_s2 = local::mk_126(taylorSimplex::ldih6_x);
const taylorFunction taylorSimplex::delta_x_126_s2 = local::mk_126(taylorSimplex::delta);

const taylorFunction taylorSimplex::dih_x_135_s2 = local::dih_x_135_s2;
const taylorFunction taylorSimplex::dih2_x_135_s2 = local::mk_135(taylorSimplex::dih2);
const taylorFunction taylorSimplex::dih3_x_135_s2 = local::mk_135(taylorSimplex::dih3);
const taylorFunction taylorSimplex::dih4_x_135_s2 = local::mk_135(taylorSimplex::dih4);
const taylorFunction taylorSimplex::dih5_x_135_s2 = local::mk_135(taylorSimplex::dih5);
const taylorFunction taylorSimplex::dih6_x_135_s2 = local::mk_135(taylorSimplex::dih6);

const taylorFunction taylorSimplex::ldih_x_135_s2 = local::mk_135(taylorSimplex::ldih_x);
const taylorFunction taylorSimplex::ldih3_x_135_s2 = local::mk_135(taylorSimplex::ldih3_x);
const taylorFunction taylorSimplex::ldih5_x_135_s2 = local::mk_135(taylorSimplex::ldih5_x);
const taylorFunction taylorSimplex::delta_x_135_s2 = local::mk_135(taylorSimplex::delta);

//
const taylorFunction taylorSimplex::ldih_x_126_n = local::ldih_x_126_n;
const taylorFunction taylorSimplex::ldih2_x_126_n=
  local::mk_126(taylorFunction::rotate2(local::ldih_x_n));
const taylorFunction taylorSimplex::ldih6_x_126_n= 
  local::mk_126(taylorFunction::rotate6(local::ldih_x_n));
const taylorFunction taylorSimplex::ldih_x_135_n=local::ldih_x_135_n;
const taylorFunction taylorSimplex::ldih3_x_135_n= 
  local::mk_135(taylorFunction::rotate3(local::ldih_x_n));
const taylorFunction taylorSimplex::ldih5_x_135_n= 
  local::mk_135(taylorFunction::rotate5(local::ldih_x_n));


const taylorFunction taylorSimplex::gamma3f_x_vLR_lfun = local::gamma3f_x_vLR_lfun;
const taylorFunction taylorSimplex::gamma3f_x_vLR0 = local::gamma3f_x_vLR0;
const taylorFunction taylorSimplex::gamma3f_x_vL_lfun = local::gamma3f_x_vL_lfun;
const taylorFunction taylorSimplex::gamma3f_x_vL0 = local::gamma3f_x_vL0;
const taylorFunction taylorSimplex::gamma3f_x_v_lfun = local::gamma3f_x_v_lfun;
const taylorFunction taylorSimplex::gamma3f_x_v0 = local::gamma3f_x_v0;

const taylorFunction taylorSimplex::gamma3f_vLR_x_nlfun = local::gamma3f_vLR_x_nlfun;
const taylorFunction taylorSimplex::gamma3f_vLR_x_n0 = local::gamma3f_vLR_x_n0;
const taylorFunction taylorSimplex::gamma3f_vL_x_nlfun = local::gamma3f_vL_x_nlfun;
const taylorFunction taylorSimplex::gamma3f_vL_x_n0 = local::gamma3f_vL_x_n0;

const taylorFunction taylorSimplex::gamma3f_135_x_s_n = local::gamma3f_135_x_s_n;
const taylorFunction taylorSimplex::gamma3f_126_x_s_n = local::gamma3f_126_x_s_n;

const taylorFunction taylorSimplex::upper_dih = local::upper_dih;

const taylorFunction taylorSimplex::num1 = local::num1;
const taylorFunction taylorSimplex::num2 = local::num2;
const taylorFunction taylorSimplex::num_combo1 = local::num_combo1_alt;

const taylorFunction taylorSimplex::edge_flat2_x = local::edge_flat2_x;
const taylorFunction taylorSimplex::taum_x = local::taum_x;
const taylorFunction taylorSimplex::flat_term_x = local::flat_term_x;


const taylorFunction taylorSimplex::dih_template_B_x(const interval& x15,const interval& x45,
					const interval& x34,const interval& x12, 
						     const interval& x25) {
  return local::dih_template_B_x( x15, x45,x34,x12,    x25);
};


const taylorFunction taylorSimplex::taum_template_B_x(const interval& x15,const interval& x45,
					const interval& x34,const interval& x12   ) {
  return local::taum_template_B_x( x15, x45,x34,x12);
};

const taylorFunction taylorSimplex::delta_template_B_x(const interval& x15,const interval& x45,
					const interval& x34,const interval& x12   ) {
  return local::delta_template_B_x( x15, x45,x34,x12);
};

const taylorFunction taylorSimplex::dih_hexall_x(const interval& x14, const interval& x12,
						 const interval & x23) {
  return local::dih_hexall_x(x14,x12,x23);
};

const taylorFunction taylorSimplex::taum_hexall_x(const interval& x14, const interval& x12,
						 const interval & x23) {
  return local::taum_hexall_x(x14,x12,x23);
};







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
/*   Section:taylorInterval                                                           */
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
      if (DD[i][j] < 0.0)  { error::message("negative DD in taylorError"); } 
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
  double absC = dabs(c); 
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
/*   Section:taylorFunction                                                           */
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

lineInterval taylorFunction::tangentAtEstimate(const domain& x) const {
  lineInterval t;
  lineInterval temp;
  for (mapPrim::const_iterator ia = this->data.begin();ia!=this->data.end();++ia) {
    temp =  ((primitive*)(ia->first))->tangentAtEstimate(x);
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
/*    Section:TESTING ROUTINES                                                        */
/*                                                                            */
/* ========================================================================== */


static int epsilonClose(double x,interval y,double epsilon)
{
  if (interMath::abs(y-interval(x,x))>epsilon)
    {
      cout << "close eps : " << interMath::abs(y-interval(x,x))
	   << " x: " << x << " y: " << y << endl<< flush;
      return 0;
    }
  return 1;
}

static int epsilonCloseDoubles(double x,double y,double epsilon)
{
  if (abs(y-x)>epsilon)
    {
      cout << "close-doubles eps: " << abs(y-x)
	   << " x: " << x << "  y: " << y << endl<< flush;
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
  
  
  /*test +,*,evalf,tangentAtEstimate */{
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
    lineInterval L = f.tangentAtEstimate(x);
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

  /* test monomial */   { 
    domain x(1.1,1.2,1.3,1.4,1.5,1.6);
    taylorInterval at = taylorSimplex::monomial(7,12,1,0,2,3).evalf(x,x);
    double mValue= 208.16588972375973;
    double mathValueD[6]={1324.692025514837,2081.6588972376016,
      160.1276074798155,0,277.5545196316802,390.3110432320503};
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "monomial  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "monomial D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

	/*test monomial DD */ {
	// constants computed in Mathematica.
	cout.precision(16);
	domain x(1.1,1.2,1.3,1.4,1.5,1.6);
	double DDmf[6][6] = {{
	    7225.592866444565,13246.920255148372,1018.9938657806439,0,
	    1766.2560340197826,2483.7975478403196},
			     {13246.920255148372,19081.87322467802,1601.2760747981552,0,
			      2775.545196316802,3903.1104323205036},
			     {1018.9938657806439,1601.2760747981552,0,0,213.50347663975396,
			      300.23926402465406},{0,0,0,0,0,0},
			     {1766.2560340197826,2775.545196316802,213.50347663975396,0,
			      185.0363464211201,520.4147243094003},
			     {2483.7975478403196,3903.1104323205036,300.23926402465406,0,
			      520.4147243094003,487.8888040400628}};
        taylorInterval g = taylorSimplex::monomial(7,12,1,0,2,3).evalf(x,x);
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
	    if (!epsilonCloseDoubles(DDmf[i][j],g.DD[i][j],1.0e-8)) {
		cout << "monomial DD " << i << " " << j << " " << g.DD[i][j];
		cout << " eps: " << (DDmf[i][j] - g.DD[i][j]) << endl;
		error::message("monomial failure");
	      }
	  }
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


  /* test chi126 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=84.6;
    double mathValueD[6]={2.68,1.4499999999999957,17.019999999999996,
			  19.269999999999996,18.9,-1.3699999999999974};
    taylorInterval at = ::chi126.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "chi126  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "chi126 D " << i << "++ fails " << at.upperPartial(i) << endl;
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

  /* test arclength_x_234 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 1.0674194068234593;
    double mathValueD[6]={0,-0.06875697006122505,
			  -0.07028159730433495,0.13431594151495124,0,0};
    taylorInterval at = taylorSimplex::arclength_x_234.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "arclength_x_234  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "arclength_x_234 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test arclength_x_126 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 1.1087112366844947;
    double mathValueD[6]={-0.07387006214108435,
			  -0.07531619563273523,0,0,0,0.13460766879042044};
    taylorInterval at = taylorSimplex::arclength_x_126.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "arclength_x_126  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "arclength_x_126 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


  /* test arclength_x_345 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 1.066957923498952;
    double mathValueD[6]={0,0,-0.06715688186243648,
			  -0.06861379768796456,0.13126117818567132,0};
    taylorInterval at = taylorSimplex::arclength_x_345.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "arclength_x_345  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "arclength_x_345 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


  /* test arclength_x1 */   { 
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 1.0965338178368775;
    double mathValueD[6]={-0.07084353197306854,0,0,0,0,0};
    taylorInterval at = taylorSimplex::arclength_x1(interval::interval("2.08"),interval::interval("2.14")).evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "arclength_x1  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "arclength_x1 D " << i << "++ fails " << at.upperPartial(i) << endl;
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

  /* test acs_sqrt_x1_d4 */   { 
    domain x(0.1,0.2,0.3,0.4,0.5,0.6);
    double mValue= 1.491656801832486;
    double mathValueD[6]={-0.396525792859072,0,0,0,0,0};
    taylorInterval at = taylorSimplex::acs_sqrt_x1_d4.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "acs_sqrt_x1_d4  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-12))
	cout << "acs_sqrt_x1_d4 D " << i << "++ fails " << at.upperPartial(i) << endl;
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

  /* test taum */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=0.11401488191744286;
      double mathValueD[6]={0.03794036469543799,0.03897627648849593,
   0.04008789744884282,0.060373310393189945,0.05954757563245067,
			    0.05861887751578681};
      taylorInterval at = local::taum.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "taum  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "taum D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test taum_x1 */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=0.05942793337929775;
      double mathValueD[6]={0.06745481394227296,0,0,0,0,0};
      taylorInterval at = taylorSimplex::taum_x1("2.08","2.14").evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "taum_x1  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "taum_x1 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


  /* test sol_x_div_sqrtdelta */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=0.04709264939663462;
      double mathValueD[6]={-0.007970124315933509,
   -0.0078097332943296155,-0.007652473097370668,
   0.0020141581396420677,0.002054235662205097,
			    0.0020953681436752004};
    taylorInterval at = taylorSimplex::sol_euler_x_div_sqrtdelta.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "sol_euler  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "sol_euler D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


  /* test dih_x_div_sqrtdelta_posbranch */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=0.09505303179216332;
      double mathValueD[6]={-0.0023705608269591763,
   -0.010018211153794957,-0.00988385942104016,0.006798828382032002,
			    -0.008648206061779122,-0.008539365987877277};
    taylorInterval at = taylorSimplex::dih_x_div_sqrtdelta_posbranch.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "dih_x_div  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "dih_x_div D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test ldih_x_div_sqrtdelta_posbranch */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=0.09051138456508404;
      double mathValueD[6]={-0.04739512815129222,-0.00953953961592741,
   -0.009411607227858571,0.006473979405766214,-0.0082349935598826,
			    -0.008131353880018816};
    taylorInterval at = taylorSimplex::ldih_x_div_sqrtdelta_posbranch.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "ldih_x_div  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "ldih_x_div D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


  /* test surfR126d */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      interval iv("1.26");
      double mValue=0.24612962297243207;
      double mathValueD[6]={-0.09070836975729879,-0.09295483666087634,
			    0,0,0,-0.05957970324319257};
      taylorInterval at = local::surfR126d(iv*iv).evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "surfR126d  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "surfR126d D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test surf_x */   {
      domain x(4.1,4.2,4.3,4.4,4.5,4.6);
      double mValue=0.8292709333317916;
      double mathValueD[6]={-0.039547523814608646,
   -0.042240250046217266,-0.04530842004702463,0.10392001499779156,
			    0.10117451454538572,0.09806905563554107};
      taylorInterval at = local::surf_x.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "surf_x  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-10))
	cout << "surf_x D " << i << "++ fails " << at.upperPartial(i) << endl;
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


  /* test ldih_x */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=1.1579692760682505;
    double mathValueD[6]={-0.5284984757448858,-0.050272297038852574,
   -0.055285815942576776,0.1507076628774728,-0.04313329060478024,
			  -0.04803311813761087};
    taylorInterval at = taylorSimplex::ldih_x.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "ldih_x  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "ldih_x D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test dih3_x_135_s2 */   {
    /* fj[y1_, y2_, y3_, y4_, y5_, y6_] := Dihedral3[y1, sqrt2, y3, sqrt2, y5, sqrt2];    testDataY[fj, xD] */
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.8978353845717557;
    double mathValueD[6]={-0.11763582712748807,0,0.04693838886383641,
			  0,-0.1291648084755952,0};
    taylorInterval at = taylorSimplex::dih3_x_135_s2.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "dih3_x_135_s2  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "dih3_x_135_s2 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test ldih2_x_126_s2 */   {
    /* fj[y1_, y2_, y3_, y4_, y5_, y6_] := Lfun[y2/2] Dihedral2[y1, y2, sqrt2, 
       sqrt2, sqrt2, y6]; */
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.7968080665440581;
      double mathValueD[6]={-0.10245354865782212,-0.37336749454984774,
			    0,0,0,-0.11599764292809825};
    taylorInterval at = taylorSimplex::ldih2_x_126_s2.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "ldih2_x_126_s2  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "ldih2_x_126_s2 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


  /* test ldih_x_126_n */    {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.8236262990441832;
      double mathValueD[6]={-0.37197051623101446,
			    -0.1065059467538398,0,0,0,-0.1182704109076129};
    taylorInterval at = taylorSimplex::ldih_x_126_n.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "ldih_x_126_n  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "ldih_x_126_n D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
    } 

  /* test ldih2_x_126_n */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.7968080665440581;
      double mathValueD[6]={-0.10245354865782212,
			    -0.37336749454984774,0,0,0,-0.11599764292809825};
    taylorInterval at = taylorSimplex::ldih2_x_126_n.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "ldih2_x_126_n  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "ldih2_x_126_n D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
    } 



  /* test gamma3f_x_vLR_lfun */  {
    /* fj[y1_, y2_, y3_, y4_, y5_, y6_] :=
    (Dihedral[y1, y2, y3, y4, y5, y6] - 
    Dihedral[y1, y2, sqrt2, sqrt2, sqrt2, y6] - Dihedral[y1, sqrt2, y3, sqrt2,
           y5, sqrt2]) *(vol2r[y1, sqrt2] - ((2*mm1/Pi)* 2*Pi*(1 - y1/(
            sqrt2*2)) - (8*mm2/Pi)*2*Pi*Lfun [y1/2]))/(2*Pi); */
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=-0.10478996414996176;
    double mathValueD[6]={0.02370215728957028,0.012021942974373388,
   0.01156437446193877,0.032219123924855125,0.015414868484842895,
			  0.015015719816071069};
    taylorInterval at = taylorSimplex::gamma3f_x_vLR_lfun.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gamma3f_x_vLR_lfun  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "gamma3f_x_vLR_lfun D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  } 

 

  /* test gamma3f_x_vLR0 */   {
    /* fj[y1_, y2_, y3_, y4_, y5_, y6_] :=
    (Dihedral[y1, y2, y3, y4, y5, y6] - 
    Dihedral[y1, y2, sqrt2, sqrt2, sqrt2, y6] - Dihedral[y1, sqrt2, y3, sqrt2,
           y5, sqrt2]) *(vol2r[y1, sqrt2] - ((2*mm1/Pi)* 2*Pi*(1 - y1/(
            sqrt2*2)) ))/(2*Pi); */
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=-0.07306777810008296;
    double mathValueD[6]={0.009716449167778748,0.008382641111760384,
   0.00806358847343414,0.022465699044914193,0.010748454768823143,
   0.010470137025369903};
    taylorInterval at = taylorSimplex::gamma3f_x_vLR0.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gamma3f_x_vLR0  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "gamma3f_x_vLR0 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test gamma3f_vLR_x_nlfun */ {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=-0.10478996414996176;
    double mathValueD[6]={0.02370215728957028,0.012021942974373388,
   0.01156437446193877,0.032219123924855125,0.015414868484842895,
			  0.015015719816071069};
    taylorInterval at = taylorSimplex::gamma3f_vLR_x_nlfun.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gamma3f_vLR_x_nlfun  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "gamma3f_vLR_x_nlfun D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
    } 


  /* test gamma3f_vLR_x_n0  */ {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=-0.07306777810008296;
    double mathValueD[6]={0.009716449167778748,0.008382641111760384,
   0.00806358847343414,0.022465699044914193,0.010748454768823143,
   0.010470137025369903};
    taylorInterval at = taylorSimplex::gamma3f_vLR_x_n0.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gamma3f_vLR_x_n0  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "gamma3f_vLR_x_n0 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
    } 

 /* test gamma3f_x_vL_lfun */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.06537057859213256;
    double mathValueD[6]={-0.016383158282497496,0.012021942974373388,
   -0.011819309789103422,0.032219123924855125,-0.009221275207565662,
   0.015015719816071069};
    taylorInterval at = taylorSimplex::gamma3f_x_vL_lfun.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gamma3f_x_vL_lfun  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "gamma3f_x_vL_lfun D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test gamma3f_vL_x_nlfun */    {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.06537057859213256;
    double mathValueD[6]={-0.016383158282497496,0.012021942974373388,
   -0.011819309789103422,0.032219123924855125,-0.009221275207565662,
   0.015015719816071069};
    taylorInterval at = taylorSimplex::gamma3f_vL_x_nlfun.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gamma3f_vL_x_nlfun  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "gamma3f_vL_x_nlfun D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
    } 

/* test gamma3f_x_vL0 */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.04558149217427438;
    double mathValueD[6]={-0.007175030424085833,0.008382641111760384,
   -0.008241349369396288,0.022465699044914193,-0.0064297959841076065,
			  0.010470137025369903};
    taylorInterval at = taylorSimplex::gamma3f_x_vL0.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gamma3f_x_vL0  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "gamma3f_x_vL0 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


  /* test gamma3f_vL_x_n0 */    {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.04558149217427438;
    double mathValueD[6]={-0.007175030424085833,0.008382641111760384,
   -0.008241349369396288,0.022465699044914193,-0.0064297959841076065,
			  0.010470137025369903};
    taylorInterval at = taylorSimplex::gamma3f_vL_x_n0.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gamma3f_vL_x_n0  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "gamma3f_vL_x_n0 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
    } 

/* test gamma3f_x_v_lfun */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.2353428720907426;
    double mathValueD[6]={-0.05636749908923225,-0.010747491782145005,
   -0.011819309789103422,0.032219123924855125,-0.009221275207565662,
			  -0.010268787639757223};
    taylorInterval at = taylorSimplex::gamma3f_x_v_lfun.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gamma3f_x_v_lfun  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "gamma3f_x_v_lfun D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

/* test gamma3f_x_v0 */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.16409950031812143;
    double mathValueD[6]={-0.024008337266888214,-0.0074939938288978115,
   -0.008241349369396288,0.022465699044914193,-0.0064297959841076065,
			  -0.007160203772423269};
    taylorInterval at = taylorSimplex::gamma3f_x_v0.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "gamma3f_x_v0  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "gamma3f_x_v0 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

/* test num_combo1 */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=106856.19915775987;
    double mathValueD[6]={129116.82713599993,-36041.29702399999,-39139.13697279997,
			  3345.7972223999877,48540.89593855997,45449.9555584};
    taylorInterval at = taylorSimplex::num_combo1.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-7))
      cout << "num_combo1  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-7))
	cout << "num_combo1 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

/* test num2 */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= -400514.3541760006;
    double mathValueD[6]={183303.01440000001,-141693.01760000008,-129522.33472000009,
   -283267.08224000037,92448.90214400007,103929.62816000001};
    taylorInterval at = taylorSimplex::num2.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-7))
      cout << "num2  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-7))
	cout << "num2 D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

/* test edge_flat2_x */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 13.47804480741523;
    double mathValueD[6]={-0.9946443990172562,
   1.0737670163683373,1.0726015670201678,0,
			  0.9263130491578268,0.927319546791744};
    taylorInterval at = taylorSimplex::edge_flat2_x.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-7))
      cout << "edge_flat2_x  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-7))
	cout << "edge_flat2_x D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

/* test dih_template_B_x */ 
/*
EdgeFlat2X[x1_, x2_, x3_, x4_, x5_, x6_] :=
    (-x1^2 + x1*x2 + x1*x3 - x2*x3 + x1*x5 + x2*x5 +
     x1*x6 + x3*x6 - x5*x6 + Sqrt[(x1^2 + (x3 - x5)^2 - 2*x1*(x3 + 
          x5))*(x1^2 + (x2 - x6)^2 - 2*x1*(x2 + x6))])/(2*x1);
EdgeFlatY[y1_, y2_, y3_, y4_, y5_, y6_] :=
    Sqrt[EdgeFlat2X[y1*y1, y2*y2, y3*y3, y4*y4, y5*y5, y6*y6]];

DihTemplateBY[y1_, y2_, y3_, y4_, y5_, y6_] := 
                  Module[{x15 , y15, x45, y45, x34, y34, x12, y12, x25, y25},
      {x15, x45, x34, x12, x25} = {4.05, 4.06, 4.07, 4.08, 4.09};
      {y15, y45, y34, y12, y25} = Sqrt[{x15, x45, x34, x12, x25}];
      Dihedral[y1, y2, y5, y25, y15, y12] -
        Dihedral[y1, y3, y4, y34, EdgeFlatY[y5, y1, y4, 0, y45, y15],
          EdgeFlatY[y2, y1, y3, 0, y12, y12]]];

testDataY[DihTemplateBY, xD];


 */  {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 0.06408402988981576;
    double mathValueD[6]={0.095233452304016,
   -0.008810715358399585,0.09112460810085135,
   0.09746406695932812,-0.007124876592996855,0};
    taylorInterval at = taylorSimplex::dih_template_B_x("4.05","4.06","4.07","4.08","4.09").evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-7))
      cout << "dih_template_B_x  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-7))
	cout << "dih_template_B_x D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


/* test test_function */  /*{
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= -1.0;
    double mathValueD[6]={0,0,0,0,0,0};
    taylorInterval at = taylorSimplex::test_function("4.05","4.06","4.07","4.08","4.09").evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-7))
      cout << "test_function  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-7))
	cout << "test_function D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
    }*/


/* test delta_template_B_x */  {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 163.7546138008497;
    double mathValueD[6]={55.01058278546959,
   18.130898957905337,36.12837433956597,
			  31.835175572865438,12.620816315612643,0};
    taylorInterval at = taylorSimplex::delta_template_B_x("4.05","4.06","4.07","4.08").evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-7))
      cout << "delta_template_B_x  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-7))
	cout << "delta_template_B_x D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


/* test taum_template_B_x */  {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 0.3452502082228403;
    double mathValueD[6]={-0.04158244346317638,
   0.1244818464673533,-0.0372665205738725,
			  -0.036269154103101636,0.10301469355600877,0};
    taylorInterval at = taylorSimplex::taum_template_B_x("4.05","4.06","4.07","4.08").evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-7))
      cout << "taum_template_B_x  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-7))
	cout << "taum_template_B_x D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test dih_hexall_x */ {
    domain x(4.1,4.2,4.3,4.4,9.1,4.5);
    double mValue= 0.27539762137268586; 
    double mathValueD[6]={0.07216262184043515,
   -0.17855993063048037,0.11332613354785265,
			  0.13711123070639236,-0.15826402277769083,0};
    taylorInterval at = taylorSimplex::dih_hexall_x("4.05","4.06","4.07").evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-7))
      cout << "dih_hexall_x  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-7))
	cout << "dih_hexall_x D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test taum_hexall_x */ {
    domain x(4.1,4.2,4.3,4.4,9.1,4.5);
    double mValue= 0.3009404994937695;
    double mathValueD[6]={-0.002236014081067203,
   0.23833890835925803,-0.08780372322878402,
			  -0.0944863574012447,0.14934344565557375,0};
    taylorInterval at = taylorSimplex::taum_hexall_x("4.05","4.06","4.07").evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-7))
      cout << "taum_hexall_x  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-7))
	cout << "taum_hexall_x D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test upper_dih */  {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue= 1.2160734358595164;
    double mathValueD[6]={0.051435930789879736,
   -0.052794842015294,-0.058059927441134945,
   0.15826981699207354,-0.04529761712139804,
			  -0.050443306412222735};
    taylorInterval at = taylorSimplex::upper_dih.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-7))
      cout << "upper_dih  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-7))
	cout << "upper_dih D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


  /* test vol3_x_sqrt */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.4652359019298107;
  double mathValueD[6]={-0.0038809463071660254,
			-0.006418488123389966,0,0,0,-0.01806132704488803};
    taylorInterval at = taylorSimplex::vol3_x_sqrt.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "vol3_x_sqrt  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "vol3_x_sqrt D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }


  /* test vol3f_x_lfun */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.4457211325536522;
    double mathValueD[6]={-0.02940386658560512,-0.029833252900862778,
			  0,0,0,-0.03280740250782458};
    taylorInterval at = taylorSimplex::vol3f_x_lfun.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "vol3f_x_lfun  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "vol3f_x_lfun D " << i << "++ fails " << at.upperPartial(i) << endl;
    }
  }

  /* test vol3f_x_sqrt2_lmplus */   {
    domain x(4.1,4.2,4.3,4.4,4.5,4.6);
    double mValue=0.4990241768945513;
    double mathValueD[6]={-0.05347687268458264,-0.03672605271672298,
      0,0,0,-0.040461569165859704};
    taylorInterval at = taylorSimplex::vol3f_x_sqrt2_lmplus.evalf(x,x); 
    if (!epsilonCloseDoubles(at.upperBound(),mValue,1.0e-8))
      cout << "vol3f_x_sqrt2_lmplus  fails " << endl;
    for (int i=0;i<6;i++) {
      if (!epsilonCloseDoubles(at.upperPartial(i),mathValueD[i],1.0e-8))
	cout << "vol3f_x_sqrt2_lmplus D " << i << "++ fails " << at.upperPartial(i) << endl;
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


    
    lineInterval al = a.tangentAtEstimate(x);
    lineInterval bl = b.tangentAtEstimate(x);
    lineInterval cl = c.tangentAtEstimate(x);
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
