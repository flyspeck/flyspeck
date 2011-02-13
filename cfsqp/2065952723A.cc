
#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"
#include "2065952723A.h"

class trialdata { public: trialdata(Minimizer M,char* s) { M.coutReport(s); };};





// The top part of the code is machine generated.
// The end is hand crafted.


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



// Start hand-crafted code.

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

// functions for 29865.. 



double delta_x_a_priori(double x1,double x2,double x3,double x4,double x5,double x6) {
  max(nglobal::delta_a_priori,delta_x(x1,x2,x3,x4,x5,x6));
}

void deltaA(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = delta_x_a_priori(4.0,4.0,4.0,a2,b2,y2);
}

void deltaAm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = - delta_x(4.0,4.0,4.0,a2,b2,y2);
}

void deltaB(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = delta_x(4.0,4.0,4.0,c2,d2,y2);
}

void deltaBm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = - delta_x(4.0,4.0,4.0,c2,d2,y2);
}

void num1A(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = num1(e1,e2,e3,y2,b2,a2);
}

void num1Am(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = - num1(e1,e2,e3,y2,b2,a2);
}

void num1B(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = num1(e4,e2,e3,y2,c2,d2);
}

void num1Bm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = - num1(e4,e2,e3,y2,c2,d2);
}

void num2Am(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = - num2(e1,e2,e3,y2,b2,a2);
}

void num2Bm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = - num2(e4,e2,e3,y2,c2,d2);
}

void dihA(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  dih_x(4.0,4.0,4.0,a2,b2,y2);
}

void dihBm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  - dih_x(4.0,4.0,4.0,d2,c2,y2);
}

void delta4A(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  delta_x4(4.0,4.0,4.0,a2,b2,y2);
}

void delta4Y(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  delta_x4(4.0,4.0,4.0,y2,a2,b2);
}

void delta4Ym(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  - delta_x4(4.0,4.0,4.0,y2,a2,b2);
}

void delta4Bm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  - delta_x4(4.0,4.0,4.0,d2,y2,c2);
}

void delta4B(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  delta_x4(4.0,4.0,4.0,d2,y2,c2);
}

void dihYdihAm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  dih_x(4.0,4.0,4.0,y2,a2,b2) - dih_x(4.0,4.0,4.0,a2,b2,y2);
}

double lindih_x(double theta,double a2,double b2,double y2) { // y2 opposite.
  double d = delta_x(4.0,4.0,4.0,a2,b2,y2);
  double x1 = 4.0;
  double d4 = delta_x4(4.0,4.0,4.0,y2,a2,b2);
  double tantheta = tan(theta);
  double t2 = tantheta*tantheta;
  return  t2 * d4 * d4 - 4.0 * x1 * d;
  // dih = pi/2 - atan (d4/sqrt(4 x1 d)).    
  /* assume theta in [0,pi/2].

      if (d4>=0),   so dih in [0,pi/2], and
     atan(d4/sqrt(4 x1 d)) = pi/2 - dih,   dih = atan(sqrt(4 x1 d)/d4),
       tan^2(dih) d4^2 - 4 x1 d =0,
       t2 d4^2 - 4 x1 d < 0 ==> tan^2 theta < tan^2(dih) ==> theta < dih.
                                    > 0 ==> dih<theta.

       if (d4<=0), so dih in [pi/2,pi].
       dih = pi/2 + atan(-d4/sqrt(4 x1 d)) = pi - atan(sqrt(4 x1 d)/(-d4)),
       tan^2(pi-dih) d4^2 - 4 x1 d = 0.
       t2 d4^2 - 4 x1 d < 0 ==> tan^2 theta < tan^2(pi-dih) ==> dih < pi - theta.
                                     >0 ==> dih > pi-theta.
  */
}



void dihB_lt_theta(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  lindih_x(nglobal::theta,y2,c2,d2); // dihB < theta, or dihB > pi - theta.
}

void dihA_lt_theta(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  lindih_x(nglobal::theta,y2,b2,a2); // dihA < theta, or dihA > pi - theta.
}

void dihY_lt_theta(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  lindih_x(nglobal::theta,a2,b2,y2); // dihY < theta, or dihY > pi - theta.
}

double rat1(double e1,double e2,double e3,double a2,double b2,double c2) {
  double afac = sqrt(a2) * (16.0 - a2); // 4 deleted Feb 6, 2011.
  double sd = sqrt(delta_x(4.0,4.0,4.0,a2,b2,c2));
  return num1(e1,e2,e3,a2,b2,c2)/(afac * sd);
}

double rat1_a_priori(double e1,double e2,double e3,double a2,double b2,double c2) {
  double afac = sqrt(a2) * (16.0 - a2); // 4 deleted Feb 6, 2011.
  double sd = sqrt(delta_x_a_priori(4.0,4.0,4.0,a2,b2,c2));
  return num1(e1,e2,e3,a2,b2,c2)/(afac * sd);
}

void rat1A(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = rat1_a_priori(e1,e2,e3,y2,b2,a2);
}

void rat1B(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  rat1(e4,e2,e3,y2,c2,d2);
}


void rat1AB(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  rat1_a_priori(e1,e2,e3,y2,b2,a2) + rat1(e4,e2,e3,y2,c2,d2);
}



void rat1Am(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = - rat1_a_priori(e1,e2,e3,y2,b2,a2) ;
}

void rat1Bm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = - rat1(e4,e2,e3,y2,c2,d2);
}

void rat1ABm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  -(rat1_a_priori(e1,e2,e3,y2,b2,a2) + rat1(e4,e2,e3,y2,c2,d2));
}

double den2(double a2,double b2,double c2) {
  double afac =  sqrt(a2) * (16.0 - a2); // Feb 6, 2011, corrected.
  double sd = sqrt(delta_x(4.0,4.0,4.0,a2,b2,c2));
  return (afac * afac* sd * sd * sd);
}

double den2_a_priori(double a2,double b2,double c2) {
  double afac =  sqrt(a2) * (16.0 - a2); // Feb 6, 2011, corrected.
  double sd = sqrt(delta_x_a_priori(4.0,4.0,4.0,a2,b2,c2));
  return (afac * afac* sd * sd * sd);
}

double rat2(double e1,double e2,double e3,double a2,double b2,double c2) {
  return num2(e1,e2,e3,a2,b2,c2)/den2(a2,b2,c2);
}

double rat2_a_priori(double e1,double e2,double e3,double a2,double b2,double c2) {
  return num2(e1,e2,e3,a2,b2,c2)/den2_a_priori(a2,b2,c2);
}

double ratsgn(double sgn, double y_mangle__[9],int parity) {
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 if (0==parity) return  -(rat2_a_priori(e1,e2,e3,y2,b2,a2) + rat2(e4,e2,e3,y2,c2,d2));
 double r1AB = rat1_a_priori(e1,e2,e3,y2,b2,a2) + rat1(e4,e2,e3,y2,c2,d2);
 return sgn * r1AB;
}

void ratcombo(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = - (1.0-fabs(nglobal::alpha)) * (rat2_a_priori(e1,e2,e3,y2,b2,a2) + rat2(e4,e2,e3,y2,c2,d2)) +
   nglobal::alpha*( rat1_a_priori(e1,e2,e3,y2,b2,a2) + rat1(e4,e2,e3,y2,c2,d2));
  }




void rat2Am(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = - rat2_a_priori(e1,e2,e3,y2,b2,a2) ;
}

void rat2Bm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret = - rat2(e4,e2,e3,y2,c2,d2);
}


void rat2ABm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  -(rat2_a_priori(e1,e2,e3,y2,b2,a2) + rat2(e4,e2,e3,y2,c2,d2));
}

void rat2A0m(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  - num2(e1,e2,e3,y2,b2,a2) - nglobal::theta * den2_a_priori(y2,b2,a2);
}

void rat2B0m(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  - num2(e4,e2,e3,y2,c2,d2) - nglobal::theta * den2(y2,c2,d2);
}


void eulerBm(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  - eulerA_x(4.0,4.0,4.0,y2,d2,c2);
}

void solidB(int numargs,int whichFn,double* y_mangle__, double* ret,void*) { 
double e1 = y_mangle__[0];
double e2 = y_mangle__[1];
double e3 = y_mangle__[2];
double e4 = y_mangle__[3];
double a2 = y_mangle__[4];
double b2 = y_mangle__[5];
double c2 = y_mangle__[6];
double d2 = y_mangle__[7];
double y2 = y_mangle__[8];
 *ret =  sol_y(2.0,2.0,2.0,sqrt(y2),sqrt(d2),sqrt(c2));
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

Minimizer m_deltaA(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = deltaA;
	M.cFunc = c0;
	return M;
};

Minimizer m_deltaAm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = deltaAm;
	M.cFunc = c0;
	return M;
};

Minimizer m_deltaB(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = deltaB;
	M.cFunc = c0;
	return M;
};

Minimizer m_deltaBm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = deltaBm;
	M.cFunc = c0;
	return M;
};

Minimizer m_num1A(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = num1A;
	M.cFunc = c0;
	return M;
};

Minimizer m_num1Am(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = num1Am;
	M.cFunc = c0;
	return M;
};

Minimizer m_num1B(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = num1B;
	M.cFunc = c0;
	return M;
};

Minimizer m_num1Bm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = num1Bm;
	M.cFunc = c0;
	return M;
};

Minimizer m_num2Am(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = num2Am;
	M.cFunc = c0;
	return M;
};

Minimizer m_num2Bm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = num2Bm;
	M.cFunc = c0;
	return M;
};

Minimizer m_dihA(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = dihA;
	M.cFunc = c0;
	return M;
};

Minimizer m_dihBm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = dihBm;
	M.cFunc = c0;
	return M;
};

Minimizer m_delta4A(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = delta4A;
	M.cFunc = c0;
	return M;
};

Minimizer m_delta4Y(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = delta4Y;
	M.cFunc = c0;
	return M;
};

Minimizer m_delta4Ym(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = delta4Ym;
	M.cFunc = c0;
	return M;
};

Minimizer m_delta4Bm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = delta4Bm;
	M.cFunc = c0;
	return M;
};

Minimizer m_delta4B(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = delta4B;
	M.cFunc = c0;
	return M;
};

Minimizer m_dihYdihAm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = dihYdihAm;
	M.cFunc = c0;
	return M;
};

Minimizer m_dihB_lt_theta(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = dihB_lt_theta;
	M.cFunc = c0;
	return M;
};

Minimizer m_dihA_lt_theta(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = dihA_lt_theta;
	M.cFunc = c0;
	return M;
};

Minimizer m_dihY_lt_theta(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = dihY_lt_theta;
	M.cFunc = c0;
	return M;
};

Minimizer m_rat1A(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = rat1A;
	M.cFunc = c0;
	return M;
};

Minimizer m_rat1Am(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = rat1Am;
	M.cFunc = c0;
	return M;
};

Minimizer m_rat2Am(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = rat2Am;
	M.cFunc = c0;
	return M;
};

Minimizer m_ratcombo(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = ratcombo;
	M.cFunc = c0;
	return M;
};


Minimizer m_rat1B(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = rat1B;
	M.cFunc = c0;
	return M;
};

Minimizer m_rat1Bm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = rat1Bm;
	M.cFunc = c0;
	return M;
};

Minimizer m_rat2Bm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = rat2Bm;
	M.cFunc = c0;
	return M;
};

Minimizer m_rat1AB(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = rat1AB;
	M.cFunc = c0;
	return M;
};

Minimizer m_rat1ABm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = rat1ABm;
	M.cFunc = c0;
	return M;
};

Minimizer m_rat2ABm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = rat2ABm;
	M.cFunc = c0;
	return M;
};

Minimizer m_rat2A0m(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = rat2A0m;
	M.cFunc = c0;
	return M;
};

Minimizer m_rat2B0m(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = rat2B0m;
	M.cFunc = c0;
	return M;
};


Minimizer m_eulerBm(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = eulerBm;
	M.cFunc = c0;
	return M;
};

Minimizer m_solidB(double xmin[9],double xmax[9]) {
	Minimizer M(nglobal::trialcount,9,0,xmin,xmax);
	M.func = solidB;
	M.cFunc = c0;
	return M;
};



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


// split on the final three variables

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


void split9(const double xmin[9],const double xmax[9],
	   double rmin[2][9],double rmax[2][9]) {  
	int j_wide=0; /* init j_wide */ {
	double w = xmax[0]-xmin[0]; 
	for (int j=0;j<9;j++) {
	  if (xmax[j]-xmin[j] > w) { j_wide = j; w = xmax[j]-xmin[j]; }
	  }
	}
	double y = (xmin[j_wide]+xmax[j_wide])/2.0;
	for (int k=0;k<2;k++) 	{
	  for (int j=0;j<9;j++) { rmin[k][j] = xmin[j]; rmax[k][j]=xmax[j]; }
	  (k? rmin[k][j_wide] = y : rmax[k][j_wide] = y);
	}
}



void print9(double xmin[9],double xmax[9]) {
  cout << "\n\nxmin : " ;
  for (int i=0;i<9;i++) { cout << ", " << xmin[i]; }
  cout << endl << "xmax : ";
  for (int i=0;i<9;i++) { cout << ", " << xmax[i]; }
  cout << endl << flush;
}


int counter = 0;
int combcounter =0;

int lastprintcount = 0;
int printspan=40;

int numerical_data::getCounter() {
  return counter;
}

void dumpdata298(double xmin[9],double xmax[9]) {
  cout << "\n\n";
  cout << "deltaA min " << m_deltaA(xmin,xmax).optimize() << endl;
  cout << "deltaA max " << - m_deltaAm(xmin,xmax).optimize() << endl;
  cout << "deltaB min " << m_deltaB(xmin,xmax).optimize() << endl;
  cout << "deltaB max " << - m_deltaBm(xmin,xmax).optimize() << endl;

  cout << "delta4Y min" << m_delta4Y(xmin,xmax).optimize() << endl;
  cout << "delta4Y max" << -m_delta4Ym(xmin,xmax).optimize() << endl;

  cout << "delta4B min" << m_delta4B(xmin,xmax).optimize() << endl;
  cout << "delta4B max" << -m_delta4Bm(xmin,xmax).optimize() << endl;


  cout << "num1A min " <<  m_num1A(xmin,xmax).optimize() << endl;
  cout << "num1A max " <<  - m_num1Am(xmin,xmax).optimize() << endl;
  cout << "num1B min " <<  m_num1B(xmin,xmax).optimize() << endl;
  cout << "num1B max " <<  - m_num1Bm(xmin,xmax).optimize() << endl;

  cout << "num2A max " <<  - m_num2Am(xmin,xmax).optimize() << endl;
  cout << "num2B max " <<  - m_num2Bm(xmin,xmax).optimize() << endl;

  cout << "rat1A min " <<  m_rat1A(xmin,xmax).optimize() << endl;
  cout << "rat1A max " <<  - m_rat1Am(xmin,xmax).optimize() << endl;
  cout << "rat1B min " <<  m_rat1B(xmin,xmax).optimize() << endl;
  cout << "rat1B max " <<  - m_rat1Bm(xmin,xmax).optimize() << endl;
  cout << "rat1AB min " <<  m_rat1AB(xmin,xmax).optimize() << endl;
  cout << "rat1AB max " <<  - m_rat1ABm(xmin,xmax).optimize() << endl;

  cout << "rat2A max " <<  - m_rat2Am(xmin,xmax).optimize() << endl;
  cout << "rat2B max " <<  - m_rat2Bm(xmin,xmax).optimize() << endl;
  cout << "rat2AB max " <<  - m_rat2ABm(xmin,xmax).optimize() << endl;

  cout << "eulerB max " <<  - m_eulerBm(xmin,xmax).optimize() << endl;
  cout << "solidB min " <<   m_solidB(xmin,xmax).optimize() << endl;
  cout << "dihA min" << m_dihA(xmin,xmax).optimize() << endl;

}

void print_strategy(numerical_data::n298 o) {
  switch(o) {
  case numerical_data::neg_deltaA : cout << "neg_deltaA"; break;
  case numerical_data::neg_deltaB : cout << "neg_deltaB"; break;
  case numerical_data::neg_num1 : cout << "neg_num1"; break;
  case numerical_data::pos_num1 : cout << "pos_num1"; break;
  case numerical_data::neg_num2 : cout << "neg_num2"; break;
  case numerical_data::reflexAB : cout << "reflexAB"; break;
  case numerical_data::angleYA : cout << "angleYA"; break;
  case numerical_data::angleYB : cout << "angleYB"; break;
  case numerical_data::neg_rat1 : cout << "neg_rat1"; break;
  case numerical_data::rat_combo : cout << "rat_combo"; break;
  case numerical_data::pos_rat1 : cout << "pos_rat1"; break;
  case numerical_data::neg_rat2 : cout << "neg_rat2"; break;
  case numerical_data::neg_rat2_A0 : cout << "neg_rat2_A0"; break;
  case numerical_data::eulerB : cout << "eulerB"; break;
  case numerical_data::solidB : cout << "solidB"; break;
  case numerical_data::split : cout << "split"; break;
  default : cout << "unknown"; break;
  }
  cout << endl << flush;
}

numerical_data::n298 numerical_data::setStrategy298(double xmin[9],double xmax[9],double* cut,numerical_data::case298 caseno) {
    int debug = 0;

    /*
  double nglobal::eps = 0.001; // 
  double nglobal::mid = nglobal::eps;
  double nglobal::big = nglobal::eps;  // completes in 2032 steps.

  nglobal::eps=0.001; nglobal::mid=1; nglobal::big=1; // completes in 2084 steps.
  nglobal::eps=0.01; nglobal::mid=1; nglobal::big=5; // completes in 2293 steps.
  nglobal::eps=0.02; nglobal::mid=3; nglobal::big=10; // completes in 2491 steps.
  nglobal::eps=0.04; nglobal::mid=6; nglobal::big=20; //  completes in 4477 steps.
  nglobal::eps=0.1; nglobal::mid=6; nglobal::big=20; // completes in 4477 steps.
  nglobal::eps=0.2; nglobal::mid=6; nglobal::big=20; // completes in 4477 steps.  // old Feb < 2/9 runs.

  nglobal::eps=0.001; nglobal::mid=nglobal::eps; nglobal::big=nglobal::eps;   // 22735 steps brings it to 87% .  Much worse! Use quads!
  // 93775 steps to 91%.  
  
  // benchmarks with rat_combo added in.
  nglobal::eps=0.001; nglobal::mid=nglobal::eps; nglobal::big=nglobal::eps;   // 500s 46%,  // aborted, more bugs corrected 2/10/2011.
  nglobal::eps=0.001; nglobal::mid=nglobal::eps; nglobal::big=nglobal::eps;   // 500s 49%, completes in 26553 steps.

  nglobal::eps=0.001; nglobal::mid=nglobal::eps; nglobal::big=nglobal::eps; // top1401, completes in 876 steps.
  nglobal::eps=0.2; nglobal::mid=6; nglobal::big=20; // top1401, completes in 1689 steps

  // benchmarks for subcases.

  if (numerical_data::top1401==caseno) {
    nglobal::eps=0.4; nglobal::mid=10; nglobal::big=40; // *top1401, completes in 3300 steps.
  }

  if (numerical_data::topit==caseno) {
  nglobal::eps=0.2; nglobal::mid=10; nglobal::big=10; // topit, completes in 915 steps
  nglobal::eps=0.2; nglobal::mid=10; nglobal::big=20; // *topit, completes in 1432 steps
  }

  if (numerical_data::dih_constraint==caseno) {
    nglobal::eps=0.4; nglobal::mid=10; nglobal::big=40; // dih..., 37% after 500 steps, 40% after 1583 steps.
  nglobal::eps=0.2; nglobal::mid=10; nglobal::big=10; //   45% after 1579 steps. 72% after 6200 steps.
  nglobal::eps=0.1; nglobal::mid=5; nglobal::big=10; // 74% after 2097 steps.  76% after 3215 steps.
  nglobal::eps=0.05; nglobal::mid=4; nglobal::big=5; // 74% after 2000 steps, 78% after 6161 steps.

  // retry with nglobal::delta_a_priori truncation.
  nglobal::delta_a_priori=21.4; // 
  nglobal::eps=0.05; nglobal::mid=4; nglobal::big=5; // completes in 2039 steps.
  nglobal::eps=0.2; nglobal::mid=10; nglobal::big=10; //  *completes in 3931 steps.
  }

  if (numerical_data::pent_acute==caseno) {
  // retry with nglobal::delta_a_priori truncation.
  nglobal::delta_a_priori=25.7; // 
  nglobal::eps=0.05; nglobal::mid=4; nglobal::big=5; //  completes in 3005 steps.
  nglobal::eps=0.2; nglobal::mid=10; nglobal::big=10; //  completes in 4351 steps.
  }
    */

    /*
  if (numerical_data::top1401==caseno) {
    nglobal::eps=0.4; nglobal::mid=10; nglobal::big=40; // *top1401, completes in 3300 steps.
  }

  if (numerical_data::topit==caseno) {
  nglobal::eps=0.2; nglobal::mid=10; nglobal::big=20; // *topit, completes in 1432 steps
  }

  if (numerical_data::dih_constraint==caseno) {
  nglobal::delta_a_priori=21.4; // 
  nglobal::eps=0.2; nglobal::mid=10; nglobal::big=10; //  *completes in 3931 steps.
  }

  if (numerical_data::pent_acute==caseno) {
  nglobal::delta_a_priori=25.7; // 
  nglobal::eps=0.2; nglobal::mid=10; nglobal::big=10; //  completes in 4351 steps.
  }
    */

  double eps = nglobal::eps;  double mid=nglobal::mid; double big = nglobal::big;
  

  /* deltaA < 0 */ 
  double v_deltaAm = m_deltaAm(xmin,xmax).optimize() ;

  if (v_deltaAm > eps) 
    { return numerical_data::neg_deltaA; }
  
  /* deltaB < 0 */
  if (m_deltaBm(xmin,xmax).optimize() > eps) 
    { return numerical_data::neg_deltaB; }

  /* deltaA < delta_a_priori */
  if ((numerical_data::dih_constraint==caseno || numerical_data::pent_acute==caseno) && 
      v_deltaAm + nglobal::delta_a_priori > eps) 
    { return numerical_data::small_deltaA; }

  /* dihY > v_dih_constraint. */
  double v_delta4Ym =  m_delta4Ym(xmin,xmax).optimize();
  if (numerical_data::dih_constraint==caseno && v_delta4Ym > eps) {
    nglobal::theta = pi() - nglobal::v_dih_constraint;
    if (m_dihY_lt_theta(xmin,xmax).optimize() > eps) 
    { return numerical_data::big_dihY; }
  }

  /* delta4Y > 0 */
  if (numerical_data::pent_acute==caseno && v_delta4Ym > eps) {
    return numerical_data::delta4Y; 
  }

  double vA,vB;
  /* num1A > 0 and num1B >0 */ {
    vA = m_num1A(xmin,xmax).optimize();
    vB = m_num1B(xmin,xmax).optimize();
    if (vA > big && vB > big) { return numerical_data::pos_num1; }
  }

  /* num1A < 0 and num1B <0 */ 
  if (vA < - eps && vB < - eps) {
    if (m_num1Am(xmin,xmax).optimize() > big && 
	m_num1Bm(xmin,xmax).optimize() > big) 
      { return numerical_data::neg_num1; }
  }

  /* num2A < 0 and num2B <0 */  
  if ( m_num2Am(xmin,xmax).optimize() > big &&
       m_num2Bm(xmin,xmax).optimize() > big )
    { return numerical_data::neg_num2; }

  double v_deltaA  = m_deltaA(xmin,xmax).optimize();
  double v_delta4Bm  = m_delta4Bm(xmin,xmax).optimize();

  /* dihA > c and dihB > pi -c */ 
  if (v_deltaA > mid && v_delta4Bm > eps) {
    double dihA = m_dihA(xmin,xmax).optimize();
    nglobal::theta = dihA - eps;
    if (m_dihB_lt_theta(xmin,xmax).optimize() >  eps) 
      { *cut = nglobal::theta; return numerical_data::reflexAB; }
  }
    
  double v_deltaB =  m_deltaB(xmin,xmax).optimize();
  double v_delta4A =  m_delta4A(xmin,xmax).optimize();

  /* solidB > t[6,0]/2 + 2 sol0.  */ 
  if (v_deltaB > mid && (numerical_data::top1401==caseno)) {
    if (m_solidB(xmin,xmax).optimize() > 1.4815 + eps) { return numerical_data::solidB; }
    // tameTableD[6,0]/2 + 2 sol0 approx 1.48147. // hexcase.
  }
  
  /* dihA + dihB < dihY, deltaA ~ 0. */
  if (v_deltaB > mid && v_delta4A > eps && v_delta4Ym > eps) {
    double v_dihB_max = - m_dihBm(xmin,xmax).optimize() + eps;
    double c = (pi() - v_dihB_max)/3.0;
    if ( (nglobal::theta = c, m_dihA_lt_theta(xmin,xmax).optimize() > eps)  &&
	 (nglobal::theta = 2.0*c, m_dihY_lt_theta(xmin,xmax).optimize() > eps) ) 
      { *cut = c;  return numerical_data::angleYA; }
  }
  
  double v_delta4B = m_delta4B(xmin,xmax).optimize();

  /* dihA + dihB < dihY, deltaB ~ 0. */
  if (v_deltaA > mid && v_delta4B > eps) {
    nglobal::theta = m_dihYdihAm(xmin,xmax).optimize() -eps;
    if (m_dihB_lt_theta(xmin,xmax).optimize() > eps) 
      { *cut = nglobal::theta; return numerical_data::angleYB; }
  }

  /* dihA + dihB < dihY, deltaA ~ 0, deltaB ~ 0 */
  if (v_delta4Ym > eps && v_delta4B > eps && v_delta4A > eps) {
    nglobal::theta = pi()/ 4.0;
    if (m_dihA_lt_theta(xmin,xmax).optimize() > eps &&
	m_dihB_lt_theta(xmin,xmax).optimize() > eps )
      { *cut = nglobal::theta; return numerical_data::angleYAB; }
  }

  /* rat1A + rat1B > 0 */
  if (v_deltaA > mid && v_deltaB > mid) {
    double v_rat1A = m_rat1A(xmin,xmax).optimize();
    if (v_rat1A + m_rat1B(xmin,xmax).optimize() > eps) 
      { *cut = v_rat1A; return numerical_data::pos_rat1; }
  }

  /* rat1A + rat1B < 0 */
  if (v_deltaA > mid && v_deltaB > mid) {
    double v_rat1Am = m_rat1Am(xmin,xmax).optimize();
    if (v_rat1Am + m_rat1Bm(xmin,xmax).optimize() > eps) 
      { *cut = v_rat1Am; return numerical_data::neg_rat1; }
  }

  /* rat2A + rat2B < 0 */ 
  if (v_deltaA > mid && v_deltaB > mid) {
    double v_rat2Am = m_rat2Am(xmin,xmax).optimize();
    if (v_rat2Am + m_rat2Bm(xmin,xmax).optimize() > eps) 
      { *cut = v_rat2Am; return numerical_data::neg_rat2; }
  }

  /* rat2A + rat2B < 0,  deltaA ~ 0 */ 
  if (v_deltaB > mid) {
    double v_rat2Bm =  m_rat2Bm(xmin,xmax).optimize();
    nglobal::theta = eps - v_rat2Bm;
    if (m_rat2A0m(xmin,xmax).optimize() > eps)
      { *cut = v_rat2Bm; return numerical_data::neg_rat2_A0; }
  }

  /* rat2A + rat2B < 0,  deltaB ~ 0 */ 
  if (v_deltaA > mid || (nglobal::delta_a_priori > mid))  {
    double v_rat2Am =  m_rat2Am(xmin,xmax).optimize();
    nglobal::theta = eps - v_rat2Am;
    if (m_rat2B0m(xmin,xmax).optimize() > eps)
      { *cut = v_rat2Am; return numerical_data::neg_rat2_B0; }
  }

  /* eulerB < 0 */
  if (m_eulerBm(xmin,xmax).optimize() > eps)
    { return numerical_data::eulerB; }

  /* (rat2A + rat2B)*(1-t) + sign1 * t* (rat1A + rat1B) < 0 */ 
  if (v_deltaA > mid && v_deltaB > mid) {
    double sign1; {
      Minimizer m_rat2ABmx = m_rat2ABm(xmin,xmax); 
    double v_rat2ABm = m_rat2ABmx.optimize();
    if (debug) { cout << "rat_combo rat2ABm " << v_rat2ABm << endl; }
    double v_rat1AB = ratsgn(1.0,m_rat2ABmx.x,1); 
    if (debug) { cout << "rat_combo rat1AB " << v_rat1AB << endl; }
    sign1 = (v_rat1AB > 0? 1.0 : -1.0);
    }
    // look for a combination of rat2 and rat1 that works.
    // generate 512= 2^9 data points:
    double data[2 * 512];
    for (int i=0;i<2;i++)
      for (int j=0;j<512;j++) {
	int u=1;
	double x[9];
	for (int k=0;k<9;k++) { 
	  int bit =  (j/u) % 2; u *= 2;  // kth bit of binary rep of j.
	  x[k]= (bit ? xmax[k] : xmin[k] ); 
	}
	data[2 * j + i] = ratsgn(sign1,x,i);
	//if (debug) { cout << "data " << 2*j + i << " " << data[2*j+i] << endl; }
      }
    nglobal::alpha = sign1 *simplex2Dalpha(data,512);
    if (debug) { cout << "rat_combo nglobal::alpha " << nglobal::alpha << endl; } 
    if (debug) { cout << "rat_combo opt " << m_ratcombo(xmin,xmax).optimize() << endl; }
    if ( m_ratcombo(xmin,xmax).optimize() > eps) { 
      *cut = nglobal::alpha;
      return numerical_data::rat_combo; 
    } 
  }

  return numerical_data::split; 
  
}



int recurse298(double xmin[9],double xmax[9],numerical_data::case298 caseno) {
  counter ++;


// main line
  double cut;
  if (!(numerical_data::split==numerical_data::setStrategy298(xmin,xmax,&cut,caseno))) {
    add_rectangle(xmin,xmax,9);
    return 1;
  }

  // print stats.
  static int lastprintcount = 0;
  static int printspan = 50; 
  static int c = 0;
  if (lastprintcount + printspan<= counter) {
   lastprintcount = counter;
   cout.precision(3);
   cout <<  counter << " ";
   cout.precision(6);
   cout << " f:" << numerical_data::percent_done() << endl << flush; 
   if (0== c++ % 10) { print9(xmin,xmax); dumpdata298(xmin,xmax); }
  } 

  // exit if narrow.
  double MINWIDTH=0.01;// 0.04 bails at 94%, MINWIDTH=0.1 bails at 92%
  double width=xmax[0]-xmin[0];
  for (int i=0;i<9;i++) {
    double w = xmax[i]-xmin[i];
    if (width < w) { width = w; }
  }
  if (width < MINWIDTH) {
    cout << "too narrow." << endl;
    print9(xmin,xmax);
    dumpdata298(xmin,xmax);
    return 0;
  }

  // subdivide recursively:
  double rmin[2][9], rmax[2][9];
  split9(xmin,xmax,rmin,rmax);
  return (recurse298(rmin[0],rmax[0],caseno) && recurse298(rmin[1],rmax[1],caseno));

}

void numerical_data::reset(numerical_data::case298 caseno) {
    nglobal::trialcount = 200;
    nglobal::v_dih_constraint = 2.7458;
    nglobal::delta_a_priori= -1.0e10;
    nglobal::alpha=0;
    nglobal::theta=0;
    nglobal::eps = 0.2; 
    nglobal::mid=10.0; 
    nglobal::big=10.0;

    switch(caseno) {
    case numerical_data::top1401:  eps=0.4;  big=40; break; 
    case numerical_data::topit:  eps=0.2;  big=20; break; 
    case numerical_data::dih_constraint: delta_a_priori=21.4;  break; 
    case numerical_data::pent_acute: delta_a_priori=25.7;  break; 
    default : break;
    }
  }



int main298(numerical_data::case298 caseno) {
  numerical_data::reset(caseno);
  double emax = 1.0 + sol0()/pi();
  double xlo = real_pow(2.0 / h0(),2.0);
  double xhi = real_pow(2.0 * h0(),2.0);
  double xp = real_pow(3.915,2.0);
  double topit= 10.0; 
  double x0[9]={1,1,1,1,     xlo,xlo,xlo,   4.0,4.0  };
  double z0[9]={emax,emax,emax,emax, xhi,xhi,xhi, xp,xp };	 
  int d2=7; int b2=5;
  switch(caseno) {
  case numerical_data::topit :  z0[d2]=topit;   break; 
  case numerical_data::top1401 :  x0[d2]=topit; z0[d2]=14.01;  break;
  case numerical_data::dih_constraint :  x0[d2]=topit;   break;
  case numerical_data::pent_acute : x0[b2]=topit; z0[b2]=xp; x0[d2]=xlo; z0[d2]=xhi; break;
  }

  numerical_data::set_rectangle(x0,z0,9);
  int r = recurse298(x0,z0,caseno);
  if (r) { cout << "\nfinished " << numerical_data::percent_done() << endl << flush; 
  }
  
  return r;
}

int main298test() {
  double x0[9]={1, 1, 1, 1, 5.87154, 5.63211, 5.39268, 12.1414, 14.2653};
  double z0[9]={1.17548, 1.17548, 1.17548, 1.17548, 6.11097, 5.87154, 5.87154, 12.4954, 14.6193};
  numerical_data::set_rectangle(x0,z0,9);
  double cut;
  print_strategy(numerical_data::setStrategy298(x0,z0,&cut,numerical_data::top1401));
  print9(x0,z0);
  dumpdata298(x0,z0);
  }


// NOW 206 STUFF:

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


int main() {
  //  main298(numerical_data::top1401);
  //main298(numerical_data::topit);
  // main298(numerical_data::dih_constraint);
  main298(numerical_data::pent_acute);
}
