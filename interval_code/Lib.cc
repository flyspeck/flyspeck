/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                            */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                     */
/* Split off from taylorData 2012-6 */
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
#include <assert.h>
}
#include "interval.h"
#include "univariate.h"
#include "lineInterval.h"
#include "wide.h"
#include "secondDerive.h"
#include "taylorData.h"
#include "functionLibraryB.h"

using namespace std;
using namespace tr1;
namespace Lib = FunctionLibrary;
using Lib;

/* ========================================================================== */
/*                                                                            */
/*   Section:FunctionLibrary                                                            */
/*                                                                            */
/* ========================================================================== */



static inline double max(double x,double y)
{ return (x>y ? x : y); }

static inline double dabs(const interval x) {
  return interMath::sup(interMath::max(x,-x));
}

static int copy(double DD[6][6],const double sec[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++)
			  DD[i][j]=sec[i][j];
  return 1;
}

static void testAbs(double DD[6][6],const char* s) {
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      if (DD[i][j] < 0) {
	error::message("negative absolute value detected " );
	cout << s << " " << DD[i][j] << " " << i << " " << j << endl;
      }
    }
}

static void intervalToAbsDouble(const interval DDx[6][6],double DD[6][6])
{
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) 	
			  DD[i][j]= dabs(DDx[i][j]);
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

/* implement promote1_to_6 */

const Function Lib::promote1_to_6(const univariate& f) {
  return Function::uni_slot(f,0);
}

/* implement unit */
const Function Lib::unit(Function::unit);

constant Function Lib::constant6(const interval& i) {
  return Lib::unit * i;
}

/*implement proj_x1,..,x6 */
constant Function Lib::proj_x1 = 
  Lib::promote1_to_6(i_pow1);
constant Function Lib::proj_x2 = 
  Function::uni_slot(i_pow1,1);
constant Function Lib::proj_x3 = 
  Function::uni_slot(i_pow1,2);
constant Function Lib::proj_x4 = 
  Function::uni_slot(i_pow1,3);
constant Function Lib::proj_x5 = 
  Function::uni_slot(i_pow1,4);
constant Function Lib::proj_x6 = 
  Function::uni_slot(i_pow1,5);

 Function Lib::rotate2(const Function& f) {
  return Function::compose
  (f,
   Lib::x2,Lib::x3,Lib::x1,
   Lib::x5,Lib::x6,Lib::x4);
 }

 Function Lib::rotate3(const Function& f) {
  return Function::compose
  (f,
   Lib::x3,Lib::x1,Lib::x2,
   Lib::x6,Lib::x4,Lib::x5);
 }

 Function Lib::rotate4(const Function& f) {
  return Function::compose
    (f,
  Lib::x4  , Lib::x2, Lib::x6,
  Lib::x1 , Lib::x5,  Lib::x3);
}

 Function Lib::rotate5(const Function& f) {
  return Function::compose
    (f,
     Lib::x5  , Lib::x3, Lib::x4,
     Lib::x2 , Lib::x6, Lib::x1);
}

 Function Lib::rotate6(const Function& f) {
   Function::compose
    (f,
     Lib::x6  , Lib::x1, Lib::x5,
     Lib::x3 , Lib::x4, Lib::x2);
}

/*implement proj_y1,...,y6 */
const Function Lib::proj_y1= Lib::promote1_to_6(i_sqrt);
const Function Lib::proj_y2= Lib::rotate2(proj_y1);
const Function Lib::proj_y3= Lib::rotate3(proj_y1);
const Function Lib::proj_y4= Lib::rotate4(proj_y1);
const Function Lib::proj_y5= Lib::rotate5(proj_y1);
const Function Lib::proj_y6= Lib::rotate6(proj_y1);

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
static const Function x1x2= Function::mk_raw(lineX1X2,setX1X2DD);


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
//primitiveA deltaPrimitive(linearization::delta,setAbsDelta);
const Function Lib::delta_x= Function::mk_raw(linearization::delta,setAbsDelta);// (&::deltaPrimitive);

/*implement vol_x */ 
static interval one("1");
static interval twelve("12");
const Function Lib::vol_x= 
  Function::uni(i_sqrt,Lib::delta_x) * constant6 (one/twelve);

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
const Function Lib::rad2= Function::mk_raw(linearization::rad2,setAbsRad2);

/*implement delta_x4*/
static int setAbsDeltaX4(const domain& x,const domain& z,double DDf[6][6]) {
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) { DDf[i][j]= 2.0; }
  // all second partials are pm 0,1,2.  
}
const Function Lib::delta_x4= 
  Function::mk_raw(linearization::delta_x4,setAbsDeltaX4);

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
const Function Lib::dih_x = Function::mk_raw(linearization::dih,setAbsDihedral);

const Function Lib::dih2_x = 
  Lib::rotate2(Lib::dih);
const Function Lib::dih3_x = 
  Lib::rotate3(Lib::dih);
const Function Lib::dih4_x = 
  Lib::rotate4(Lib::dih);
const Function Lib::dih5_x = 
  Lib::rotate5(Lib::dih);
const Function Lib::dih6_x = 
  Lib::rotate6(Lib::dih);


/*implement rhazim_x*/
const Function Lib:rhazim_x = 
  uni(i_rho,proj_y1) * dih_x;
const Function Lib::rhazim2 = 
  Lib::rotate2(Lib::rhazim_x);
const Function Lib::rhazim3 = 
  Lib::rotate3(Lib::rhazim_x);

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
const Function Lib::sol= Function::mk_raw(linearization::solid,setSol);

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
//static primitive_univariate i_halfbump1P(::i_halfbump_x,0);
//static primitive_univariate i_halfbump4P(::i_halfbump_x,3);
const Function Lib::halfbump_x1 = 
  Function::uni_slot(::i_halfbump_x,0);//(&::i_halfbump1P);
const Function Lib::halfbump_x4 = 
  Function::uni_slot(::i_halfbump_x,3);//(&::i_halfbump4P);


/* implement gchi (univariate) */ 
// gchi (sqrt x) = &4 * mm1 / pi -(&504 * mm2 / pi)/ &13 +(&200 * (sqrt x) * mm2 /pi)/ &13
static interval i_gchi_c0("0.974990367692870754241952463595");
static interval i_gchi_c1("0.124456752559607807811255454313");
univariate i_gchi = univariate::i_sqrt* i_gchi_c1 + univariate::i_pow0 * i_gchi_c0;


const Function Lib::gchi1_x = 
  uni(::i_gchi,proj_y1) * dih_x;



/* ========================================================================== */
/*                                                                            */
/*   Section:Lib local namespace                                            */
/*                                                                            */
/* ========================================================================== */


namespace local {

 Function operator*(const Function& f,const Function& g) {
   return Function::product(f,g);
 }

 Function operator/(const Function& f,const Function& g) {
   return Function::product(f,uni(i_inv,g));
 }

  static const Function operator*(const Function& t,int j) {
    return t * interval(j * 1.0, j * 1.0);
  }

  static const Function operator*(int j,const Function& t) {
    return t * interval(j * 1.0, j * 1.0);
  }

  static const Function operator-
  (const Function& u,const Function& t) {
    return u + t * mone;
  }


  Function uni(const univariate& u,const Function& f) {
   return Function::uni_compose(u,f);
  };

  Function y1 = Lib::y1;
  Function y2 = Lib::y2;
  Function y3 = Lib::y3;
  Function y4 = Lib::y4;

  Function x1 = Lib::x1;
  Function x2 = Lib::x2;
  Function x3 = Lib::x3;
  Function x4 = Lib::x4;
  Function x5 = Lib::x5;
  Function x6 = Lib::x6;

  Function delta_x = Lib::delta_x;
  Function delta_x4 = Lib::delta_x4;
  Function dih = Lib::dih;
  Function unit = Lib::unit;

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

  static const Function two_unit = unit * two;

   };


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



void Lib::selfTest()
{
  cout << " -- loading functionLibrary routines " << endl;
  cout << " -- done loading functionLibrary" << endl << flush;
  
}
