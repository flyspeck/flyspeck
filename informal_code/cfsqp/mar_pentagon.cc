// Test on Feb 16, 2012 to compute scaledVoronoi Phelan-Weaire foam.
// Revise Feb 21, for sectional Voronoi representation.

#include <iomanip.h>
#include <iostream.h>
#include "Minimizer.h"
#include <math.h>
#include "numerical.h"
#include "assert.h"

double myrand();

double findMinimumEQ(int numargs, int nconstr,
	double* xmin, double* xmax, double* x,
        void (*func)(int numargs,int whichFn,double* x,double* ret,void*),
		     void (*cFunc)(int numargs,int which,double* x,double* ret,void*));


// constructor calls optimizer.  No need to place in main loop.
class trialdata {
public:
  trialdata(Minimizer M,char* s) {
    M.coutReport(s);
  };
};

//constraint rad < sqrt2():
/*
void smallrad(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = rady(y[0],y[1],y[2],y[3],y[4],y[5]) - (sqrt2());
};
*/

////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
/*
void t1(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = vol3(y[0],y[1],y[2]) -vol3M(y[0],y[1],y[2]) + eps;
	}
Minimizer m1() {
  double xmin[3]= {2,2,2};
  double xmax[3]= {sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(trialcount,3,1,xmin,xmax);
	M.func = t1;
	M.cFunc = smallradf;
	return M;
}
trialdata d1(m1(),"ID[HJKDESR3] d1: Marchal main 3-cell inequality");
*/

////////// NEW INEQ PENTAGON-PACKING 2015

// vars 
// y[0]=alpha;
// y[1]=beta;
// y[2]=xc;

double pinwheel_area(double alpha,double beta,double xc) {
  return area_triangle(pinwheel_a(alpha,beta,xc),
		       pinwheel_b(alpha,beta,xc),
		       pinwheel_c(alpha,beta,xc));
}

// constraint alpha+beta+gamma=pi/5: // ret <= 0:
void pinwheel_constraint(int numargs,int whichFn,double* y, double* ret,void*) {
  double negval = 0.0;
         switch (whichFn) {
	 case 1: negval = y[0]+y[1]-pi()/5.0; break;
	 case 2: negval = pinwheel_area(y[0],y[1],y[2])-area_del_dl(); break;
	 case 3: negval = pinwheel_b(y[0],y[1],y[2])-pinwheel_a(y[0],y[1],y[2]); break;
	 case 4: negval = pinwheel_c(y[0],y[1],y[2])-pinwheel_a(y[0],y[1],y[2]); break;
	 case 5 : negval = - pinwheel_a(y[0],y[1],y[2]) + 1.72; break;
	 case 6 : negval = pinwheel_a(y[0],y[1],y[2]) - 1.85; break;
       default : cout << "out of bounds " << endl; break;
       }
	 *ret = negval;
};

// this is minimized.  failure reported if min is negative.
void tpin(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = pinwheel_a(y[0],y[1],y[2]);
	}
Minimizer mpin() {
  int trialcount = 100;
  //  double xmin[3]= {0.0,0.0,0.0};
  //double xmax[3]= {2.0*pi()/5.0,2.0*pi()/5.0, 2.0*pent_e()};
    double xmin[3]= {0.2,0.2,0.1};
    double xmax[3]= {0.3,0.3,0.3};

	Minimizer M(trialcount,3,4,xmin,xmax);
	M.func = tpin;
	M.cFunc = pinwheel_constraint;
	return M;
}
trialdata dpin(mpin(),"ID pin: pentagon-pinwheel acute inequality");


void tpin2(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = pinwheel_area(y[0],y[1],y[2]) - (1.28 - 0.330769 * (-1.72 + pinwheel_a(y[0],y[1],y[2]) ));
	}
Minimizer mpin2() {
  int trialcount = 100;
    double xmin[3]= {0.0,0.0,0.0};
    double xmax[3]= {2.0*pi()/5.0,2.0*pi()/5.0, 2.0*pent_e()};
  //    double xmin[3]= {0.2,0.2,0.1};
  //  double xmax[3]= {0.3,0.3,0.3};
	Minimizer M(trialcount,3,6,xmin,xmax);
	M.func = tpin2;
	M.cFunc = pinwheel_constraint;
	return M;
}
trialdata dpin2(mpin2(),"ID pin2: pentagon-pinwheel acute inequality");



// L-junction test:
double lj_area(double alpha,double beta,double xc) {
  return area_triangle(lj_a(alpha,beta,xc),
		       lj_b(alpha,beta,xc),
		       lj_c(alpha,beta,xc));
}

// constraint alpha+beta+gamma=pi/5: // ret <= 0:
void lj_constraint(int numargs,int whichFn,double* y, double* ret,void*) {
  double alpha = y[0];
  double beta = y[1];
  double xc = y[2];
  double negval = 0.0;
         switch (whichFn) {
	 case 1: negval = y[0]+y[1]-3.0*pi()/5.0; break;
	 case 2: negval = pi()/5.0 - (alpha+beta); break;
	 case 3: negval = 0*lj_area(y[0],y[1],y[2])-area_del_dl(); break;
	 case 4: negval = lj_b(y[0],y[1],y[2])-lj_a(y[0],y[1],y[2]); break;
	 case 5: negval = lj_c(y[0],y[1],y[2])-lj_a(y[0],y[1],y[2]); break;
       default : cout << "out of bounds " << endl; break;
       }
	 *ret = negval;
};

// this is minimized.  failure reported if min is negative.
void tlj(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = lj_a(y[0],y[1],y[2]) ;
	}
Minimizer mlj() {
  int trialcount = 500;
  //  double xmin[3]= {0.0,0.0,0.0};
  //double xmax[3]= {2.0*pi()/5.0,2.0*pi()/5.0, 2.0*pent_e()};
    double xmin[3]= {0.0,0.0,0.0};
    double xmax[3]= {2.0*pi()/5.0,2.0*pi()/5.0,2.0*pent_e()};

	Minimizer M(trialcount,3,5,xmin,xmax);
	M.func = tlj;
	M.cFunc = lj_constraint;
	return M;
}
trialdata dlj(mlj(),"ID lj: pentagon-lj acute inequality");

// constraint alpha+beta+gamma=pi/5: // ret <= 0:
void lj_constraint2(int numargs,int whichFn,double* y, double* ret,void*) {
  double alpha = y[0];
  double beta = y[1];
  double xc = y[2];
  double negval = 0.0;
         switch (whichFn) {
	 case 1: negval = y[0]+y[1]-3.0*pi()/5.0; break;
	 case 2: negval = pi()/5.0 - (alpha+beta); break;
       default : cout << "out of bounds " << endl; break;
       }
	 *ret = negval;
};

// this is minimized.  failure reported if min is negative.
void tlj2(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = lj_area(y[0],y[1],y[2]) ;
	}
Minimizer mlj2() {
  int trialcount = 500;
    double xmin[3]= {0.0,0.0,0.0};
    double xmax[3]= {2.0*pi()/5.0,2.0*pi()/5.0,2.0*pent_e()};

	Minimizer M(trialcount,3,2,xmin,xmax);
	M.func = tlj2;
	M.cFunc = lj_constraint2;
	return M;
}
trialdata dlj2(mlj2(),"ID lj2: pentagon-lj2 acute inequality");


// T-junction:

double tj_area(double alpha,double beta,double xc) {
  return area_triangle(tj_a(alpha,beta,xc),
		       tj_b(alpha,beta,xc),
		       tj_c(alpha,beta,xc));
}


// constraint alpha+beta+gamma=pi/5: // ret <= 0:
void tj_constraint2(int numargs,int whichFn,double* y, double* ret,void*) {
  double alpha = y[0];
  double beta = y[1];
  double xc = y[2];
  double negval = 0.0;
         switch (whichFn) {
	 case 1: negval = y[0]+y[1]-pi(); break;
	 case 2: negval = 3.0*pi()/5.0 - (alpha+beta); break;
	 case 3: negval = alpha+beta - 4.0*pi()/5.0; break;
       default : cout << "out of bounds " << endl; break;
       }
	 *ret = negval;
};

// this is minimized.  failure reported if min is negative.
void ttj2(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = tj_area(y[0],y[1],y[2]) ;
	}
Minimizer mtj2() {
  int trialcount = 500;
  double xmin[3]= {pi()/5.0,pi()/5.0,pi()/5.0};
    double xmax[3]= {2.0*pi()/5.0,2.0*pi()/5.0,2.0*pent_e()};
	Minimizer M(trialcount,3,3,xmin,xmax);
	M.func = ttj2;
	M.cFunc = tj_constraint2;
	return M;
}
trialdata dtj2(mtj2(),"ID tj2: pentagon-tj2 acute inequality");

// constraint alpha+beta+gamma=pi/5: // ret <= 0:
void tj_constraint(int numargs,int whichFn,double* y, double* ret,void*) {
  double alpha = y[0];
  double beta = y[1];
  double xc = y[2];
  double negval = 0.0;
         switch (whichFn) {
	 case 1: negval = y[0]+y[1]-pi(); break;
	 case 2: negval = 3.0*pi()/5.0 - (alpha+beta); break;
	 case 3: negval = alpha+beta - 4.0*pi()/5.0; break;
	 case 4: negval = 0*tj_area(y[0],y[1],y[2])-area_del_dl(); break;
	 case 5: negval = tj_a(y[0],y[1],y[2])-tj_c(y[0],y[1],y[2]); break;
	 case 6: negval = tj_b(y[0],y[1],y[2])-tj_c(y[0],y[1],y[2]); break;
       default : cout << "out of bounds " << endl; break;
       }
	 *ret = negval;
};

// this is minimized.  failure reported if min is negative.
void ttj(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = tj_c(y[0],y[1],y[2]) ;
	}
Minimizer mtj() {
  int trialcount = 500;
  double xmin[3]= {pi()/5.0,pi()/5.0,pi()/5.0};
    double xmax[3]= {2.0*pi()/5.0,2.0*pi()/5.0,2.0*pent_e()};
	Minimizer M(trialcount,3,6,xmin,xmax);
	M.func = ttj;
	M.cFunc = tj_constraint;
	return M;
}
trialdata dtj(mtj(),"ID tj: pentagon-tj acute inequality");


int main() {
  // test against Mathematica:
  cout << "\n";
  cout << "a: " << pinwheel_a(0.1,0.2,0.11) << endl;
  cout << "b: " << pinwheel_b(0.1,0.2,0.11) << endl;
  cout << "c: " << pinwheel_c(0.1,0.2,0.11) << endl;
  cout << "area del dl " << area_del_dl() << endl;
  cout << "l a: " << lj_a(0.1,0.2,0.15) << endl;
  cout << "l b: " << lj_b(0.1,0.2,0.15) << endl;
  cout << "l c: " << lj_c(0.1,0.2,0.15) << endl;

  cout << "t a: " << tj_a(0.1,0.2,0.15) << endl;
  cout << "t b: " << tj_b(0.1,0.2,0.15) << endl;
  cout << "t c: " << tj_c(0.1,0.2,0.15) << endl;

  }
