#include <iomanip>
#include <iostream>
#include <cmath>
#include <cassert>
#include <cstdlib>
#include  "Minimizer.h"
#include "numerical.h"
#include "2065952723A.h"

#define exec_206A // executable form.

using namespace std;

class trialdata { public: trialdata(Minimizer M,char* s) { M.coutReport(s); };};




// The top part of the code is machine generated.
// The end is hand crafted.

/***************************************************
MACHINE GENERATED DEFINITIONS FROM HOL-LIGHT
 ***************************************************/


double sol0(

) { 
return ( ((3. * (acos((1. / 3.)))) - (pi())) ); 
}


double delta_x4(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( ((((-x2) * x3) - (x1 * x4)) + ((x2 * x5) + (((x3 * x6) - (x5 * x6)) + (x1 * ((-x1) + (x2 + ((x3 - x4) + (x5 + x6)))))))) ); 
}


double dih_x(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (((pi()) / 2.) + (atn2( (sqrt((4. * (x1 * (delta_x(x1,x2,x3,x4,x5,x6)))))),(-(delta_x4(x1,x2,x3,x4,x5,x6)))))) ); 
}


double const1(

) { 
return ( ((sol_y(2.,2.,2.,2.,2.,2.)) / (pi())) ); 
}

double dih4_y(
double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (dih_y(y4,y2,y6,y1,y5,y3)) ); 
}


double dih5_y(
double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (dih_y(y5,y1,y6,y2,y4,y3)) ); 
}


double dih6_y(
double y1,double y2,double y3,double y4,double y5,double y6
) { 
return ( (dih_y(y6,y1,y5,y3,y4,y2)) ); 
}


double num1(
double e1,double e2,double e3,double a2,double b2,double c2
) { 
return ( ((-4.) * (((real_pow(a2,2.)) * e1) + ((8. * ((b2 - c2) * (e2 - e3))) - (a2 * ((16. * e1) + (((b2 - 8.) * e2) + ((c2 - 8.) * e3))))))) ); 
}

double num1m(
double e1,double e2,double e3,double a2,double b2,double c2
) { 
  return -num1(e1,e2,e3,a2,b2,c2);
}


double num2(
double e1,double e2,double e3,double a2,double b2,double c2
) { 
return ( (8. * ((2. * ((real_pow(a2,5.)) * e1)) + (((-256.) * ((real_pow((b2 + ((-1.) * c2)),3.)) * (e2 + ((-1.) * e3)))) + (((-1.) * ((real_pow(a2,3.)) * ((2. * (((-256.) + ((real_pow(b2,2.)) + (((-2.) * (b2 * c2)) + (real_pow(c2,2.))))) * e1)) + (((((real_pow(b2,2.)) * ((-8.) + c2)) + (((-16.) * (b2 * (3. + c2))) + (16. * (16. + (9. * c2))))) * e2) + (((b2 * (144. + (((-16.) * c2) + (real_pow(c2,2.))))) + ((-8.) * ((-32.) + ((6. * c2) + (real_pow(c2,2.)))))) * e3))))) + (((real_pow(a2,4.)) * (((-64.) * e1) + ((-6.) * ((((-8.) + b2) * e2) + (((-8.) + c2) * e3))))) + (((-2.) * ((real_pow(a2,2.)) * ((b2 + ((-1.) * c2)) * (((real_pow(b2,2.)) * e2) + ((8. * (c2 * ((4. * e1) + ((9. * e2) + ((-7.) * e3))))) + ((384. * (e2 + ((-1.) * e3))) + (((-1.) * ((real_pow(c2,2.)) * e3)) + (b2 * (((-32.) * e1) + (((56. + ((-9.) * c2)) * e2) + (9. * (((-8.) + c2) * e3)))))))))))) + (16. * (a2 * ((b2 + ((-1.) * c2)) * (((real_pow(b2,2.)) * (e2 + ((-3.) * e3))) + (((-4.) * (b2 * ((8. * e1) + ((((-20.) + (3. * c2)) * e2) + ((-3.) * (((-4.) + c2) * e3)))))) + (c2 * ((32. * e1) + ((3. * ((16. + c2) * e2)) + ((-1.) * ((80. + c2) * e3)))))))))))))))) ); 
}


double num_combo1(
double e1,double e2,double e3,double a2,double b2,double c2
) { 
return ( ((2. / 25.) * (((-2.) * ((real_pow(a2,5.)) * e1)) + ((256. * ((real_pow((b2 + ((-1.) * c2)),3.)) * (e2 + ((-1.) * e3)))) + (((real_pow(a2,3.)) * ((2. * (((-256.) + ((real_pow(b2,2.)) + (((-2.) * (b2 * c2)) + (real_pow(c2,2.))))) * e1)) + (((((real_pow(b2,2.)) * ((-8.) + c2)) + (((-16.) * (b2 * (3. + c2))) + (16. * (16. + (9. * c2))))) * e2) + (((b2 * (144. + (((-16.) * c2) + (real_pow(c2,2.))))) + ((-8.) * ((-32.) + ((6. * c2) + (real_pow(c2,2.)))))) * e3)))) + ((2. * ((real_pow(a2,4.)) * ((32. * e1) + (3. * ((((-8.) + b2) * e2) + (((-8.) + c2) * e3)))))) + ((200. * (real_pow((((real_pow(a2,2.)) * e1) + ((8. * ((b2 + ((-1.) * c2)) * (e2 + ((-1.) * e3)))) + ((-1.) * (a2 * ((16. * e1) + ((((-8.) + b2) * e2) + (((-8.) + c2) * e3))))))),2.))) + ((2. * ((real_pow(a2,2.)) * ((b2 + ((-1.) * c2)) * (((real_pow(b2,2.)) * e2) + ((8. * (c2 * ((4. * e1) + ((9. * e2) + ((-7.) * e3))))) + ((384. * (e2 + ((-1.) * e3))) + (((-1.) * ((real_pow(c2,2.)) * e3)) + (b2 * (((-32.) * e1) + (((56. + ((-9.) * c2)) * e2) + (9. * (((-8.) + c2) * e3)))))))))))) + ((-16.) * (a2 * ((b2 + ((-1.) * c2)) * (((real_pow(b2,2.)) * (e2 + ((-3.) * e3))) + (((-4.) * (b2 * ((8. * e1) + ((((-20.) + (3. * c2)) * e2) + ((-3.) * (((-4.) + c2) * e3)))))) + (c2 * ((32. * e1) + ((3. * ((16. + c2) * e2)) + ((-1.) * ((80. + c2) * e3))))))))))))))))) ); 
}



double num2m(
double e1,double e2,double e3,double a2,double b2,double c2
) { 
  return - num2(e1,e2,e3,a2,b2,c2);
}

double eulerA_x(
double x1,double x2,double x3,double x4,double x5,double x6
) { 
return ( (((sqrt(x1)) * ((sqrt(x2)) * (sqrt(x3)))) + (((sqrt(x1)) * ((x2 + (x3 - x4)) / 2.)) + (((sqrt(x2)) * ((x1 + (x3 - x5)) / 2.)) + ((sqrt(x3)) * ((x1 + (x2 - x6)) / 2.))))) ); 
}


/***************************************************
START OF HAND-CRAFTED CODE.   BASIC CFSQP functions
 ***************************************************/


int near(double x,double y)
  { double eps = 1.0e-8; return (mabs(x-y)<eps); } 

void selfTest() {
  assert(near (sol0(),0.5512855984325308));
}


void c0(int numargs,int whichFn,double* y_mangle__, double* ret,void*) {
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
switch(whichFn) {
default: *ret = 0; break; }}


void t_num1m(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
*ret = (0.000000e+00) + (((num1m(e1,e2,e3,a2,b2,c2)) - 0.)) + (0.0);
}


void t_num1(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
*ret = (0.000000e+00) + (((num1(e1,e2,e3,a2,b2,c2)) - 0.)) + (0.0);
}


void t_num2m(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
*ret = (0.000000e+00) + (((num2m(e1,e2,e3,a2,b2,c2)) - 0.)) + (0.0);
}

void t_combo(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
*ret = (0.000000e+00) + (((num_combo1(e1,e2,e3,a2,b2,c2)) - 0.)) + (0.0);
}


void t_varcombo(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
 *ret = (1.0-fabs(nglobal::alpha)) * num2m(e1,e2,e3,a2,b2,c2) +
              nglobal::alpha*num1(e1,e2,e3,a2,b2,c2);
  }

double numsgn(double sgn, double y_mangle__[6],int parity) {
  double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double a2 = y_mangle__[3];
double b2 = y_mangle__[4];
double c2 = y_mangle__[5];
 if (0==parity) return num2m(e1,e2,e3,a2,b2,c2);
 if (sgn>0) return num1(e1,e2,e3,a2,b2,c2);
 return num1m(e1,e2,e3,a2,b2,c2);
}


Minimizer m_num1m(double xmin[6],double xmax[6]) {
	Minimizer M(nglobal::trialcount,6,0,xmin,xmax);
	M.func = t_num1m;
	M.cFunc = c0;
	return M;
}

Minimizer m_num1(double xmin[6],double xmax[6]) {
	Minimizer M(nglobal::trialcount,6,0,xmin,xmax);
	M.func = t_num1;
	M.cFunc = c0;
	return M;
}

Minimizer m_num2m(double xmin[6],double xmax[6]) {
	Minimizer M(nglobal::trialcount,6,0,xmin,xmax);
	M.func = t_num2m;
	M.cFunc = c0;
	return M;
}


Minimizer m_combo(double xmin[6],double xmax[6]) {
	Minimizer M(nglobal::trialcount,6,0,xmin,xmax);
	M.func = t_combo;
	M.cFunc = c0;
	return M;
};

Minimizer m_varcombo(double xmin[6],double xmax[6]) {
	Minimizer M(nglobal::trialcount,6,0,xmin,xmax);
	M.func = t_varcombo;
	M.cFunc = c0;
	return M;
};

/***************************************************
CONVEX HULL IN PLANE
 ***************************************************/


/* A simple simplex method for 2-d.
The data is a list of length 2*n,
d00 d01 d10 d11 d20 d21 ....
(0,dj0) and (1,dj1) are two points determining a line.
The problem is to form the lower hull of these lines between x=0 and x=1, and to compute the highest point on the hull.  The return
value (between 0 and 1) is the x coordinate of this highest point.

For example, if n=2, and the data is (1,4,3,2), the two lines
are those passing through
(0,1) (1,4) and
(0,3) (1,2) respectively.

The lines meet at (0.5,2.5), and the procedure returns 0.5.

But if the data is (1,4,2,3), the procedure returns 1.0.
 */

double simplex2Dalpha(const double* data, int n) {

  // convert data to pairs.
  double d[n][2];
  double slope[n];
  for (int i=0;i<n;i++) {
    d[i][0] = data[2*i];
    d[i][1] = data[2*i+1];
    slope[i] = d[i][1]-d[i][0];
  }
 
  int p=0;  // pivot.
  double dmin = d[p][0];
  for (int i=0;i<n;i++) {
    if (d[i][0] < dmin || (d[i][0]==dmin && slope[i]< slope[p])) 
      { p = i; dmin = d[i][0]; }
  }
  double alpha = 0;
  
  // compute alpha, beta.   // alpha = beta/(1+beta).
  int counter = 500;
  while (counter--) {
    if (d[p][1] <= d[p][0]) return alpha; // peak has been reached.
    if (!counter) { 
      cout << "simplex resources expended" << flush; 
      exit(0); }
    double alphamin = 1.0;
    int q = -1; // new pivot
    for (int i=0;i<n;i++) {
      if (d[i][1] < d[p][1] && d[i][0] > d[p][0]) {
	double betatemp = (d[i][0]-d[p][0])/(d[p][1]-d[i][1]);
	double alphatemp = betatemp/ (1.0 + betatemp);
	if (alpha < alphatemp && 
	    (alphatemp < alphamin || 
	     (alphatemp==alphamin && (q>=0) && slope[i] < slope[q])))
	  { q=i; alphamin = alphatemp; }
      }
    }
    if (q < 0) {  // no new pivot found.
      assert(alphamin==1.0);
      return alphamin;  
    }
    assert(alphamin >= alpha); // alpha sequence should be increasing!
    // set new pivot and repeat
    p = q; alpha= alphamin;
  }
  
}

/***************************************************
RECTANGLES
 ***************************************************/
double rectangle_partial=0;
double rectangle_total=0;

double rectangle(double xmin[],double xmax[],int size) {
  double v = 1;
  for (int i=0;i<size;i++) { v *= (xmax[i] - xmin[i]); }
  return v;
}

void add_rectangle(double xmin[],double xmax[],int size) {
  rectangle_partial += rectangle(xmin,xmax,size);
}


double numerical_data::percent_done() {
  return rectangle_partial / rectangle_total;
}

void numerical_data::set_rectangle(double xmin[],double xmax[],int size) {
  rectangle_total = rectangle(xmin,xmax,size);
}

/***************************************************

 ***************************************************/

int counter = 0;
int combcounter =0;

int lastprintcount = 0;
int printspan=40;

int numerical_data::getCounter() {
  return counter;
}

// bisection split on the final three variables

int split3(const double xmin[6],const double xmax[6],
	   double rmin[2][6],double rmax[2][6]) {  
	int j_wide=0; /* init j_wide */ {
	double w = xmax[0]-xmin[0]; 
	for (int j=0;j<6;j++) {
	  if (xmax[j]-xmin[j] > w) { j_wide = j; w = xmax[j]-xmin[j]; }
	  }
	//cout << w << " " << j_wide << endl << flush;
	}
	double y = (xmin[j_wide]+xmax[j_wide])/2.0;
	for (int k=0;k<2;k++) 	{
	  for (int j=0;j<6;j++) { rmin[k][j] = xmin[j]; rmax[k][j]=xmax[j]; }
	  (k? rmin[k][j_wide] = y : rmax[k][j_wide] = y);
	}
	return j_wide;
}

/***************************************************
206 A1 SPECIFIC ROUTINES
 ***************************************************/

int setStrategy (double xmin[6],double xmax[6],numerical_data::strategy& s,int recurse)
{
  counter ++;
  double eps = 10.0; // was 0.01.

  Minimizer zer1 = m_num1(xmin,xmax);
  Minimizer zer1m = m_num1m(xmin,xmax);
  Minimizer zer2m = m_num2m(xmin,xmax);

  double m1 = zer1.optimize();
  double m1m = zer1m.optimize();
  double m2m = zer2m.optimize();
  double mm = max(m2m,max(m1,m1m));
  int which = (mm==m1 ? 1 : (mm==m1m ? 2 : 3));
  if (mm > eps) { 
    switch (which) {
    case 1 : s.mode = numerical_data::strategy::n1; break;
    case 2: s.mode = numerical_data::strategy::n1m; break;
    default : s.mode = numerical_data::strategy::n2m; break;
    }
    rectangle_partial += rectangle(xmin,xmax,6); 
    return 1; 
  }

  // check for a C/E.
  double mc = m_combo(xmin,xmax).optimize();
  if (mc < 0) {
    cout << "CE found: " << mc << flush << endl;
    for (int i=0;i<6;i++) cout << xmin[i] << " " << xmax[i] << endl;
    exit(0);
  }

  // look for a combination of num2 and num1 that works.
  // set sign of num1
  {
  double sign1 = (numsgn(1.0,zer2m.x,1) > 0.0 ? 1.0 : -1.0);
  // generate 64= 2^6 data points:
  double data[2 * 64];
  for (int i=0;i<2;i++)
    for (int j=0;j<64;j++) {
      int u=1;
      double x[6];
      for (int k=0;k<6;k++) { 
	int bit =  (j/u) % 2; u *= 2;  // kth bit of binary rep of j.
	x[k]= (bit ? xmax[k] : xmin[k] ); 
      }
      data[2 * j + i] = numsgn(sign1,x,i);
    }
  nglobal::alpha = sign1 *simplex2Dalpha(data,64);
  }

  // check if it works
  Minimizer znn = m_varcombo(xmin,xmax);
  double nn = znn.optimize();
  if (nn > eps) { 
    s.mode = numerical_data::strategy::merge;
    s.alpha = nglobal::alpha;
    combcounter++; 
    rectangle_partial += rectangle(xmin,xmax,6); 
    return 1; } 
  
  // print some statistics
  double w = 0;
  for (int i=0;i<5;i++) { w += xmax[i]-xmin[i]; }
  if (mm < 0 && (lastprintcount + printspan<= counter)) {
      cout.precision(3);
      lastprintcount = counter;
      cout << "w: " << which << " " << counter << " " <<  combcounter << " " << mm/w << " " << nn/w << " w:" << w << " a:" << nglobal::alpha ;
      cout.precision(6);
      cout << " f:" << numerical_data::percent_done() << endl << flush; } 

  // subdivide recursively:
  double rmin[2][6], rmax[2][6];
  s.mode = numerical_data::strategy::split;
  s.splitvar =split3(xmin,xmax,rmin,rmax);
  return (recurse ? (setStrategy(rmin[0],rmax[0],s,recurse) && 
		     (setStrategy(rmin[1],rmax[1],s,recurse))) : 0);;
}

int numerical_data::setStrategy206A (double xmin[6],double xmax[6],numerical_data::strategy& s) {
  return setStrategy(xmin,xmax,s,0);
}

int main206A()  { // constant changed to 15.53 on Jan 21, 2011.

  double xmin[6]= {
1.,1.,1.,(real_pow((2. / (h0())),2.)),(real_pow((2. / (h0())),2.)),(real_pow((2. / (h0())),2.))
};
  double xmax[6]= {
(1. + ((sol0()) / (pi()))),(1. + ((sol0()) / (pi()))),(1. + ((sol0()) / (pi()))),15.53,(real_pow(4.,2.)),(real_pow(4.,2.))
};

  rectangle_total = rectangle(xmin,xmax,6);
  cout << "r: " << rectangle_total << endl;
  numerical_data::strategy s;
  setStrategy(xmin,xmax,s,1);  // this does the cases.
  //  setStrategy(xmin,xmax,s,0);

  {
  double data[4] = {1.0,4.0,2.0,3.0};
  assert(1.0==simplex2Dalpha(data,2));
  }

  {
  double data[4] = {1.0,4.0,3.0,2.0};
  assert(0.5==simplex2Dalpha(data,2));
  }

  {
    double data[8] = {0.99,10.0,1.0,9.0,11.0,12.0,9.0,1.0};
  assert(0.5==simplex2Dalpha(data,4));
  }

  nglobal::alpha = 0.99915589538304627748 ;
  double y[6]={0.99999999999999988898,0.99999999999999988898,0.99999999999999988898,2.5195263290501368481,2.5195263290501368481,7.8392912459240529088};
  double r;
  t_varcombo(6,1,y,&r,0);
  
  cout.precision(30);
  cout << "alpha " << nglobal::alpha << endl;
  cout << "combo " << r << endl;
  cout << "num1 " << numsgn(1.0,y,1) << endl;
  cout << "num2 " << numsgn(1.0,y,0) << endl;

}

/***************************************************
MAIN
 ***************************************************/


#ifdef exec_206A

int main() {
  return main206A();
}

#endif
