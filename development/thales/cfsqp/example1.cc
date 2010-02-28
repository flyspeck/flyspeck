#include "Minimizer.h"

void testFunction(int numargs,int whichFn,double* x,double* ret,void*) {
	*ret = -x[0]*x[0]-x[1]*x[1];
};

int main() {
	//Test example to find the max of -Gamma on [2,2.51]^6.
  double xmin[2]= {2,5.0};
  double xmax[2]= {3.0,6.0};
	Minimizer M(800,2,0,xmin,xmax);
	M.func = testFunction;
	M.coutReport("done with test1");
}
