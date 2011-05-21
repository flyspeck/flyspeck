/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 2010-09-07 */
/* ========================================================================== */

//#include <map>
#include <utility>
#include <tr1/unordered_map>
#include <iomanip>
#include <iostream>
extern "C"
{
#include <math.h>
#include <stdlib.h>
#include <float.h>
#include <time.h>
}
#include "error.h"
#include "interval.h"
#include "univariate.h"

using namespace std;
using namespace tr1;

class uniprimitive
{
private:
	interval (*f)(const interval&);
	interval (*df)(const interval&);
	interval (*ddf)(const interval&);

public:

  interval eval(const interval&,int n) const;

  uniprimitive(interval (*)(const interval& ),interval(*) (const interval&),
		interval(*) (const interval&));

};

interval uniprimitive::eval(const interval& x,int n) const
{
  return (n ==0 ?  (*f)(x) : (n == 1 ? (*df)(x) : (*ddf)(x) ) );
}

uniprimitive::uniprimitive(interval (*f0)(const interval& ),interval(*df0) (const interval&),
	     interval(*ddf0) (const interval&)) {
  f = f0;
  df = df0;
  ddf = ddf0;
}

//sqrt 

static interval usqrt(const interval& x) {
  return interMath::sqrt(x);
}

static interval Dsqrt(const interval& x) {
	static const interval one("1");
	static const interval two("2");
	if (interMath::boundedFromZero(x))
	  {	return one/(two * interMath::sqrt(x)); }
	error::printTime ("sqrt derivative at 0 ");
	cout << x.lo << " " << x.hi << endl << flush;
	throw unstable::x;
}

static interval DDsqrt(const interval& x) {
	static const interval one("1");
	static const interval four("4");
	if (interMath::boundedFromZero(x))
	  {	return - one/(four * x * interMath::sqrt(x)); }
	error::printTime ("D2 sqrt at 0 ");
	cout << x.lo << " " << x.hi << endl << flush;
	throw unstable::x;
}


static uniprimitive psqrt(usqrt,Dsqrt,DDsqrt);


//  sqp

static inline double trunc01(double x) {
  return (x > 1.0 ? 1.0 : (x < 0.0 ? 0.0 : x));
}

static interval sqp_small(const interval& x) { // monotonic increasing.
  double t = trunc01(interMath::inf(x));
  interMath::down();
  double st = 1.0/8.0 + (11.0*t)/5.0 + ((- 119.0 * t)*t)/40.0 + (47.0*t*t*t)/20.0 +
    ((((- 7.0*t)*t)*t)*t)/10.0;
  double u = trunc01(interMath::sup(x));
  interMath::up();
  double su = 1.0/8.0 + (11.0*u)/5.0 + ((- 119.0 * u)*u)/40.0 + (47.0*u*u*u)/20.0 +
    ((((- 7.0*u)*u)*u)*u)/10.0;
  if (su < st) { error::fatal("inverted interval in sqp_small"); }
  interval s(st,su);
  return s;
}

static interval Dsqp_small(const interval& x) { // monotonic decreasing.
  double t = trunc01(interMath::sup(x));
  interMath::down();
  double st = 11.0/5.0 + (- 119.0*t)/20.0 + (141.0*t*t)/20.0 + (((- 14*t)*t)*t)/5.0;
  double u = trunc01(interMath::inf(x));
  interMath::up();
  double su = 11.0/5.0 + (- 119.0*u)/20.0 + (141.0*u*u)/20.0 + (((- 14*u)*u)*u)/5.0;
 interval s(su,st);
 if (su < st) { error::fatal("inverted interval in Dsqp_small"); }  
  return s;
}

static interval DDsqp_small(const interval& x) {  // unique max at (47/56=0.8392...,-0.0330...)
  double t = trunc01(interMath::inf(x));
  double u = trunc01(interMath::sup(x));
  ( (t > 0.8393)  ? interMath::up() : interMath::down() );
  double st = (-119.0)/20.0 + (141.0*t)/10.0 + ((- 42*t) * t)/5.0;
  ( (u < 0.8392) ? interMath::up() : interMath::down() );
  double su = (-119.0)/20.0 + (141.0*u)/10.0 + ((- 42*u) * u)/5.0;
  interval s(min(st,su),max(st,su));
  if ((t > 0.8393) || (u < 0.8392)) return s; // monotonic regions.
  // so     t <= 0.8393,  0.8392 <= u,  t <= u, st su both rounded down, v gives upper end.
 static const interval v("-0.0330357142857142857142857142857");
 return interMath::combine(v,s);
}

static interval usqp(const interval& x) {
  if (interMath::inf(x) >= 1.0) return interMath::sqrt(x);
  if (interMath::sup(x) <= 1.0) return sqp_small(x);
  interval xplus(1.0,interMath::sup(x));
  interval splus = interMath::sqrt(xplus);
  interval sminus = sqp_small(x);
  return interMath::combine(sminus,splus);
}

static interval Dusqp(const interval& x) {
  if (interMath::inf(x) >= 1.0) return Dsqrt(x);
  if (interMath::sup(x) <= 1.0) return Dsqp_small(x);
  interval xplus(1.0,interMath::sup(x));
  interval splus = Dsqrt(xplus);
  interval sminus = Dsqp_small(x);
  return interMath::combine(sminus,splus);
}


static interval DDusqp(const interval& x) {
  if (interMath::inf(x) >= 1.0) return DDsqrt(x);
  if (interMath::sup(x) <= 1.0) return DDsqp_small(x);
  interval xplus(1.0,interMath::sup(x));
  interval splus = DDsqrt(xplus);
  interval sminus = DDsqp_small(x);
  return interMath::combine(sminus,splus);
}

static uniprimitive psqp(usqp,Dusqp,DDusqp);

// sqn

static interval sqn_small(const interval& x) { // monotonic increasing.
  double t = trunc01(interMath::inf(x));
  interMath::down();
  double st = (127.0*t)/40.0 + ((-27.0*t)*t)/4.0 + (363.0*t*t*t)/40.0 
    + ((((- 61.0*t)*t)*t)*t) /10.0 +  (8.0*t*t*t*t*t)/5.0;
  double u = trunc01(interMath::sup(x));
  interMath::up();
  double su =  (127.0*u)/40.0 + ((-27.0*u)*u)/4.0 + (363.0*u*u*u)/40.0 
    + ((((- 61.0*u)*u)*u)*u) /10.0 +  (8.0*u*u*u*u*u)/5.0;
  if (su < st) { 
    cout << "x : " << interMath::inf(x);
    cout << " " << interMath::sup(x) << endl;
    cout << "st: " << st << endl;
    cout << "su: " << su << endl;
    error::fatal("inverted interval in sqn_small"); 
  }
  interval s(st,su);
  return s;
}

static interval Dsqn_small(const interval& x) { // monotonic decreasing.
  double t = trunc01(interMath::sup(x));
  interMath::down();
  double st = 127.0/40.0 + (-27.0*t)/2.0 + (1089.0*t*t)/40.0 
  +  ((( - 122.0*t)*t)*t)/5.0 + 8.0*t*t*t*t;
  double u = trunc01(interMath::inf(x));
  interMath::up();
  double su = 127.0/40.0 + (-27.0*u)/2.0 + (1089.0*u*u)/40.0 
   +  ((( - 122.0*u)*u)*u)/5.0 + 8.0*u*u*u*u;
 interval s(su,st);
 if (su < st) { error::fatal("inverted interval in Dsqn_small"); }  
  return s;
}

static interval DDsqn_small(const interval& x) {  
  // increasing on [0,0.6], f[0.6,1.0] subset [-0.47,-0.24].
  double t = trunc01(interMath::inf(x));
  double u = trunc01(interMath::sup(x));
  interMath::down();
  double st = (-27.0)/2.0 + (1089.0*t)/20.0 + ((- 366.0*t)*t)/5.0 + 32.0*t*t*t;
  interMath::up();
  double su = (-27.0)/2.0 + (1089.0*u)/20.0 + ((- 366.0*u)*u)/5.0 + 32.0*u*u*u;
  interval s(min(st,su),max(st,su));
  if (u < 0.6) return s; // monotonic regions.
  static const interval v(-0.47,-0.24);
 return interMath::combine(v,s);
}

static interval usqn(const interval& x) {
  if (interMath::inf(x) >= 1.0) return interMath::sqrt(x);
  if (interMath::sup(x) <= 1.0) return sqn_small(x);
  interval xplus(1.0,interMath::sup(x));
  interval splus = interMath::sqrt(xplus);
  interval sminus = sqn_small(x);
  return interMath::combine(sminus,splus);
}

static interval Dusqn(const interval& x) {
  if (interMath::inf(x) >= 1.0) return Dsqrt(x);
  if (interMath::sup(x) <= 1.0) return Dsqn_small(x);
  interval xplus(1.0,interMath::sup(x));
  interval splus = Dsqrt(xplus);
   interval sminus = Dsqn_small(x);
  return interMath::combine(sminus,splus);
}


static interval DDusqn(const interval& x) {
  if (interMath::inf(x) >= 1.0) return DDsqrt(x);
  if (interMath::sup(x) <= 1.0) return DDsqn_small(x);
  interval xplus(1.0,interMath::sup(x));
  interval splus = DDsqrt(xplus);
  interval sminus = DDsqn_small(x);
  return interMath::combine(sminus,splus);
}

static uniprimitive psqn(usqn,Dusqn,DDusqn);


//pow3h2

static interval upow3h2(const interval& x) {
  return interMath::sqrt(x) * x;
}

static interval Dpow3h2(const interval& x) {
	static const interval th("1.5");
	return interMath::sqrt(x) * th;
}

static interval DDpow3h2(const interval& x) {
	static const interval tq("0.75");
	return tq/(interMath::sqrt(x));
}


static uniprimitive ppow3h2(upow3h2,Dpow3h2,DDpow3h2);

//inv

static interval uinv(const interval& x) {
  static interval one("1");
  if (interMath::boundedFromZero(x)) {
    return one/x; }
  error::printTime ("inv at 0 ");
  cout << x.lo << " " << x.hi << endl << flush;
  throw unstable::x;
}

static interval Dinv(const interval& x) {
  static const interval one("1");
  if (interMath::boundedFromZero(x)) {	return - one/(x * x);     }
  error::printTime ("D inv at 0 ");
  cout << x.lo << " " << x.hi << endl << flush;
  throw unstable::x;
}

static interval DDinv(const interval& x) {
	static const interval two("2");
  if (interMath::boundedFromZero(x)) {	return two/(x * x * x);  }
  if (0) { error::printTime ("D2 inv at 0 ");  // debug.
    cout << x.lo << " " << x.hi << endl << flush; }
  throw unstable::x;
}

static uniprimitive pinv(uinv,Dinv,DDinv);


// atan 
static interval uatan(const interval& x) {
  return interMath::atan(x);
}

static interval Datan(const interval& x) {
	static const interval one("1");
	return one/(one + x * x);
}

static interval DDatan(const interval& x) {
	static const interval one("1");
	static const interval two("2");
	interval t = one + x*x;
	return - two*x /(t*t);
}

static uniprimitive patan(uatan,Datan,DDatan);

//

static interval umatan(const interval& x) {
  // switch to the power series and error term if x is small.
  // radius of convergence is 1.
  if (x.lo < 1.0e-16) {
    if (x.lo < -0.9) { throw unstable::x; }
    if (x.hi >  0.9) { throw unstable::x; }
    static const interval one("1");
    static const interval three("3");
    static const interval five("5");
    static const interval seven("7");
    interval x2 = x * x;
    interval ax = interMath::max(x,-x);
    interval error = x * x2 / (seven * (one - ax));
    return one - x / three + x2 / five + interMath::combine(error,-error);
  }
  else {
    interval r = interMath::sqrt(x);
    return interMath::atan(r) / r;
  }
}

const interval univariate::matan(const interval& x) {
  return umatan(x);
}

static interval Dmatan(const interval& x) {
  // (2*x + 2*x^2)^(-1) - ArcTan[Sqrt[x]]/(2*x^(3/2)) 
	static const interval one("1");
	static const interval two("2");
  if (x.lo < 1.0e-8) {
    if (x.lo < -0.9) { throw unstable::x; }
    if (x.hi >  0.9) { throw unstable::x; }
    static const interval three("3");
    static const interval five("5");
    static const interval seven("7");
    interval x2 = x * x;
    interval ax = interMath::max(x,-x);
    interval error = x2 / (two * (one - ax));
    return  - one / three + two * x / five + interMath::combine(error,-error);
  }
  else {
    interval r = interMath::sqrt(x);
    return (one / (two * x + two * x * x) - 
	    interMath::atan(r) / (two * x * r));
  }
}

static interval DDmatan(const interval& x) {
  // monotonic decreasing second derivative, just return m''(-0.2).
    if (x.lo < -0.2) { throw unstable::x; }
    static const interval v("0.65");
    return interMath::combine(v,-v);
}

static uniprimitive pmatan(umatan,Dmatan,DDmatan);

// asin,

//"ASN_ATN",|- !x. -- &1 < x /\ x < &1 ==> asn x = atn (x / sqrt (&1 - x pow 2))

static void atrig_domain_check(const interval& x,char* ch) {
  if (interMath::inf(x) <= -1.0 || interMath::sup(x) >= 1.0) {
    //cout << "bad argument for atrig " << ch << endl << flush;
    //error::printTime("domain error, aborting ");
    throw  unstable::x ;
  }
} 

static interval uasin(const interval& x) {
  atrig_domain_check(x,"asin");
  static const interval one("1");
  return interMath::atan(x / usqrt(one - x * x));
}

static interval Dasin(const interval& x) {
  atrig_domain_check(x,"Dasin");
  static const interval one("1");
  return one/usqrt(one - x*x);
}

static interval DDasin(const interval& x) {
  atrig_domain_check(x,"DDasin");
  static const interval one("1");
  interval t = one  - x* x;
  return x / (t * usqrt(t));
}

 static uniprimitive pasin(uasin,Dasin,DDasin);

//acos

// "ACS_ASN", |- !x. -- &1 <= x /\ x <= &1 ==> acs x = pi / &2 - asn x);

static interval uacos(const interval& x) {
  static interval pi2("1.570796326794896619");
  atrig_domain_check(x,"acos");
  return pi2 - uasin(x);
}

static interval Dacos(const interval& x) {
  atrig_domain_check(x,"Dacos");
  return - Dasin(x);
}

static interval DDacos(const interval& x) {
  atrig_domain_check(x,"DDacos");
  return - DDasin(x);
}

static uniprimitive pacos(uacos,Dacos,DDacos);

// sin , cos

static void trig_domain_check(const interval& x,char* ch) {
  static double pi_minus_eps = 4.5; // needs to be less than 3Pi/2.
  if (interMath::inf(x) <= -pi_minus_eps || interMath::sup(x) >= pi_minus_eps) {
    //cout << "bad argument for trig " << ch << endl << flush;
    //cout << "[" << x.lo << "," << x.hi << "]" << endl << flush;
    //error::printTime("domain error ");
    throw  unstable::x; 
  }
} 

 static int meets(const interval& x,const interval& y) {
   return (!(x < y)) && (!(y < x));
 }

static interval sin_p(double x) {
  interMath::up();
  double a = sin(x);
  interMath::down();
  double b = sin(x);
  interval t(min(a,b),max(a,b));
  return t;
}

static interval cos_p(double x) {
  interMath::up();
  double a = cos(x);
  interMath::down();
  double b = cos(x);
  interval t(min(a,b),max(a,b));
  return t;
}

static interval usin(const interval& x) {
  static interval one ("1");
  static interval pi2("1.570796326794896619");
  trig_domain_check(x,"sin");
  interval t = interMath::combine(sin_p(interMath::inf(x)),sin_p(interMath::sup(x)));
  t =  (meets(x,pi2) ? interMath::combine(t,one) : t);
  t = (meets(x, - pi2) ? interMath::combine(t,- one) : t);
  return t;
}

static interval ucos(const interval& x) {
  static interval zero("0");
  static interval one ("1");
  static interval mone("-1");
  static interval pi ("3.141592653589793238");
  trig_domain_check(x,"cos");
  interval t = interMath::combine(cos_p(interMath::inf(x)),cos_p(interMath::sup(x)));
  t =  (meets(x,zero) ? interMath::combine(t,one) : t);
  t =  (meets(x,pi) ? interMath::combine(t,mone) : t);
  t =  (meets(x,-pi) ? interMath::combine(t,mone) : t);
  return t;
}

static interval Dsin(const interval& x) {
  return ucos(x);
}

static interval DDsin(const interval& x) {
  return - usin(x);
}

static interval Dcos(const interval& x) {
  return - usin(x);
}

static interval DDcos(const interval& x) {
  return - ucos(x);
}

 static uniprimitive pcos(ucos,Dcos,DDcos);

 static uniprimitive psin(usin,Dsin,DDsin);

//pow0 

static interval pow0(const interval& x) {
  static const interval one("1");
  return one;
}

static interval Dpow0(const interval& x) {
	static const interval zero("0");
	return zero;
}

static interval DDpow0(const interval& x) {
	static const interval zero("0");
	return zero;
}

static uniprimitive ppow0(pow0,Dpow0,DDpow0);


//pow1 

static interval pow1(const interval& x) {
  return x;
}

static interval Dpow1(const interval& x) {
	static const interval one("1");
	return one;
}

static interval DDpow1(const interval& x) {
	static const interval zero("0");
	return zero;
}

static uniprimitive ppow1(pow1,Dpow1,DDpow1);



// pow2

static interval pow2(const interval& x) {
  return x*x;
}

static interval Dpow2(const interval& x) {
  static interval two("2");
  return two*x;
}

static interval DDpow2(const interval& x) {
  static interval two("2");
  return two;
}

 static uniprimitive ppow2(pow2,Dpow2,DDpow2);

// pow3

static interval pow3(const interval& x) {
  return x*x*x;
}

static interval Dpow3(const interval& x) {
  static interval three("3");
  return three*x*x;
}

static interval DDpow3(const interval& x) {
  static interval six("6");
  return six*x;
}

 static uniprimitive ppow3(pow3,Dpow3,DDpow3);

// pow4

static interval pow4(const interval& x) {
  return pow2(x) * pow2(x);
}

static interval Dpow4(const interval& x) {
  static interval four("4");
  return four* pow3(x);
}

static interval DDpow4(const interval& x) {
  static interval twelve("12");
  return twelve* x*x;
}

 static uniprimitive ppow4(pow4,Dpow4,DDpow4);

// IMPLEMENT UNIVARIATE CLASS


univariate::univariate(const univariate& rhs)
{
  data.clear();
  //cout << "debug : univariate construct " << endl << flush;
  for (mapType::const_iterator it = rhs.data.begin(); it!= rhs.data.end(); ++it)
      data[it->first]=it->second;
}


/*
univariate univariate::operator=(const univariate& rhs)
{
  data.clear();
  //cout << "debug : univariate = " << endl << flush;
  for (mapType::const_iterator it = rhs.data.begin(); it!= rhs.data.end(); ++it)
      data[it->first]=it->second;
}
*/

univariate::univariate(uniprimitive* p) {
  //  cout << "debug : univariate primitive " << endl << flush;
  data.clear();
  static interval one("1");
  data[p] = one;
}

univariate univariate::operator+(const univariate& rhs) const {
  univariate lhs(*this);
  mapType::iterator ilhs = lhs.data.begin();
  for (mapType::const_iterator irhs = rhs.data.begin();irhs!=rhs.data.end();++irhs) {
    ilhs = lhs.data.find(irhs->first);
    if (ilhs != lhs.data.end()) {      
      lhs.data[irhs->first] = ilhs->second + irhs->second;    
    }
    else {      lhs.data[irhs->first] = irhs->second;    }
  }
  return lhs;
}

univariate univariate::operator*(const interval& x) const  {
  univariate a(*this);
  for (mapType::const_iterator ia = a.data.begin();ia!=a.data.end();++ia) {
    a.data[ia->first] = ia->second * x;
  }
  return a;
}

univariate::~univariate() {};

interval univariate::eval(const interval& x, int n) const {
  interval t("0");
  for (mapType::const_iterator ia = this->data.begin();ia!=this->data.end();++ia) {
    t = t + (*((uniprimitive*)(ia->first))).eval(x,n) * ia->second;
  }
  return t;
};

const univariate univariate::i_pow0(&ppow0);
const univariate univariate::i_pow1(&ppow1);
const univariate univariate::i_pow2(&ppow2);
const univariate univariate::i_pow3(&ppow3);
const univariate univariate::i_pow4(&ppow4);
const univariate univariate::i_sqrt(&psqrt);
const univariate univariate::i_sqp(&psqp);
const univariate univariate::i_sqn(&psqn);
const univariate univariate::i_pow3h2(&ppow3h2);
const univariate univariate::i_inv(&pinv);
const univariate univariate::i_atan(&patan);
const univariate univariate::i_matan(&pmatan);
const univariate univariate::i_asin(&pasin);
const univariate univariate::i_acos(&pacos);
const univariate univariate::i_sin(&psin);
const univariate univariate::i_cos(&pcos);

// TESTING ROUTINES.


static int epsilonClose(double x,double y,double epsilon)
    {
      double t = abs(y-x);
      if (t>epsilon)
        {
	  cout << "close : " << t << " " << x << " " << y << endl<< flush;
        return 0;
        }
    return 1;
    }


static int epsilon3(double* f,const univariate & u) {
  interval x("0.21");
  for (int i=0;i<3;i++) {
  epsilonClose(f[i],interMath::sup(u.eval(x,i)),1.0e-8);
  }
}

/* (* Mathematica code used for testing *)
testUni[f_] := Module[{},
      	xsub = {x -> 0.21};
              Table[D[f, {x, i}], {i, 0, 2}] /. xsub]
      ];
 */
void univariate::selfTest() 
	{
	cout << " -- loading univariate routines " << endl;
	double pow0d[3]={1, 0, 0};
        epsilon3(pow0d,univariate::i_pow0);
	double pow1d[3]={0.21, 1, 0};
        epsilon3(pow1d,univariate::i_pow1);
	double pow2d[3]={0.0441, 0.42, 2};
        epsilon3(pow2d,univariate::i_pow2);
	double pow3d[3]={0.009260999999999998,0.13229999999999997,1.26};
        epsilon3(pow3d,univariate::i_pow3);
	double pow4d[3]={0.0019448099999999995,0.037043999999999994,0.5291999999999999};
        epsilon3(pow4d,univariate::i_pow4);
	double sqrtd[3]={0.458257569495584,1.0910894511799618,-2.5978320266189567};
        epsilon3(sqrtd,univariate::i_sqrt);
	double sqpd[3]={0.476204483, 1.23547420, -3.3594400};
        epsilon3(sqpd,univariate::i_sqp);
	double sqnd[3]={0.4419086901599999,1.33021258,-4.9972680};
        epsilon3(sqnd,univariate::i_sqn);

	double pow3h2d[3]={0.09623408959407263,0.687386354243376,1.6366341767699426};
        epsilon3(pow3h2d,univariate::i_pow3h2);
	double invd[3]={4.761904761904762,-22.67573696145125,215.95939963286907};
        epsilon3(invd,univariate::i_inv);

	double atand[3]={0.206992194219821,0.9577626664112633,-0.3852699165719094};
        epsilon3(atand,univariate::i_atan);
	double matand[3]={0.9376815458267412,-0.26484586865477544,/*fudge*/0.65};
        epsilon3(matand,univariate::i_matan);
	double asind[3]={0.2115749597580956,1.0228071826600218,0.22469872199874943};
        epsilon3(asind,univariate::i_asin);
	double acosd[3]={1.3592213670368012,-1.0228071826600218,-0.22469872199874943};
        epsilon3(acosd,univariate::i_acos);
	double sind[3]={0.20845989984609956,0.9780309147241483,-0.20845989984609956};
        epsilon3(sind,univariate::i_sin);
	double cosd[3]={0.9780309147241483,-0.20845989984609956,-0.9780309147241483};
        epsilon3(cosd,univariate::i_cos);
	univariate t = univariate::i_pow2 + univariate::i_atan * "3.4";
	double td[3]= {0.7478734603473914,3.676393065798295,0.690082283655508};
	        epsilon3(td,t);
interval i_gchi_c0("0.974990367692870754241952463595");
 interval i_gchi_c1("0.124456752559607807811255454313");
 univariate i_gchi = univariate::i_sqrt * i_gchi_c1 + univariate::i_pow0 * i_gchi_c0;
	}


