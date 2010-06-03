

//cut from packing.cc
////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
void t0(int numargs,int whichFn,double* y, double* ret,void*) {
  *ret = vol4(y[0],y[1],y[2],y[3],y[4],y[5]) -vol4M(y[0],y[1],y[2],y[3],y[4],y[5]) + eps;
	}
Minimizer m0() {
  double xmin[6]= {2,2,2,2,2,2};
  double xmax[6]= {sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0)};
	Minimizer M(trialcount,6,0,xmin,xmax);
	M.func = t0;
	//M.cFunc = smallrad;
	return M;
}
trialdata d0(m0(),"ID[HJKDESR4] d0: Marchal main 4-cell inequality, no rad constraint");


////////// NEW INEQ
// this is minimized.  failure reported if min is negative.
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
