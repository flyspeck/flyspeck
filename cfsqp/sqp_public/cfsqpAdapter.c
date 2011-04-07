#include "cfsqpusr.h"
#include <time.h>
#include <stdlib.h>

// header: 
double myrand();

// inequality constraints.
double minimize(int numargs, int nconstr,
	double* xmin, double* xmax, double* x,
        void (*func)(int numargs,int whichFn,double* x,double* ret,void*),
	void (*cFunc)(int numargs,int which,double* x,double* ret,void*));

// equality constraints with given initial search point.
double findMinimumEQ(int numargs, int nconstr, 
	double* xmin, double* xmax, double* x,
        void (*func)(int numargs,int whichFn,double* x,double* ret,void*),
	void (*cFunc)(int numargs,int which,double* x,double* ret,void*)) ;



// implementation

double myrand()
	{
	static int w =0;
	if (w==0) { srand(48222257 /* random but fixed seed *//* time(0) */); w = 1; }
	double u = double(rand());
	double v =  double(/*stdlib.h*/RAND_MAX); 
	return u/v;
	}


/**
 * This procedure invokes cfsqp to minimize 
 * 	func on the domain from xmin to xmax,
 * 	subject to constraints cFunc, 
 * 	and returns the result in x.
 * This procedure is the only invocation of cfsqp in the package.
 * @param numargs size of the arrays xmin, xmax, x;
 * @param nconstr number of constraints
 * @param xmin lower endpoints of the search interval (read-only).
 * @param xmax upper endponts of the search interval (read-only).
 * @param x the coordinates of the solution (write-only array).
 * @param func function being minimized passed as a pointer.
 * @param func.numargs size of the array x
 * @param func.whichFn, not used here. See cfsqp documentation for general use.
 * @param func.x, input variables of function
 * @param func.x, return value of function.
 * @param cFunc constraint function, passed as a pointer.
 * @param cFunc.numargs, size of the array x.
 * @param cFunc.whichFn, which constraint is being invoked 1,2,etc.
 * @param cFunc.x, variables of the constraint.
 * @param cFunc.ret, value of constaint,
 */ 
double minimize(int numargs, int nconstr,
	double* xmin, double* xmax, double* x,
        void (*func)(int numargs,int whichFn,double* x,double* ret,void*),
        void (*cFunc)(int numargs,int which,double* x,double* ret,void*)) {

   int i,nparam,nf,nineq,neq,mode,iprint,miter,neqn,nineqn,
       ncsrl,ncsrn,nfsr,mesh_pts[1],inform;
   double bigbnd,eps,epsneq,udelta;
   double *f,*g,*lambda;
   double r[1]={0};
   void *cd;

   mode=100;    // C=1, B=0, A=0.
   iprint=0;    // print a little bit of stuff
   miter=500;   // max number of iterations ; default 100;
   bigbnd=1.e10;  // a big number
   eps=1.e-9;     // a small number default 1.e-8;
   epsneq=0.e0;
   udelta=0.e0;
   nparam=numargs; // number of variables
   nf=1;			// number of objective functions
   nineq=nineqn=nconstr; // number of nonlinear inequality constraints
   neqn=0;			// number of nonlinear equality constraints
   neq=0;			// total number of equality constraints
   ncsrl=ncsrn=nfsr=mesh_pts[0]=0;
   f=(double *)calloc(nf,sizeof(double));
   g=(double *)calloc(nineq+neq,sizeof(double));
   lambda=(double *)calloc(nineq+neq+nf+nparam,sizeof(double));
	cd = NULL;
   
	for (i=0;i<numargs;i++) x[i]=xmin[i]+(xmax[i]-xmin[i])*myrand();
	
   cfsqp(nparam,nf,nfsr,nineqn,nineq,neqn,neq,ncsrl,ncsrn,mesh_pts,
         mode,iprint,miter,&inform,bigbnd,eps,epsneq,udelta,xmin,xmax,x,
         f,g,lambda,func,cFunc,grobfd,grcnfd,cd);
   free(f);
   free(g);
   free(lambda);
   (*func)(numargs,1,x,r,cd);
	return r[0];
}


// minimize with equality constraints.





/**
 * This procedure invokes cfsqp to minimize 
 * 	func on the domain from xmin to xmax,
 *      starting with initial value x,
 * 	subject to equality constraints cFunc, 
 * 	and returns the result in x.
 * This procedure is the only invocation of cfsqp in the package.
 * @param numargs size of the arrays xmin, xmax, x;
 * @param nconstr number of constraints
 * @param xmin lower endpoints of the search interval (read-only).
 * @param xmax upper endponts of the search interval (read-only).
 * @param x the coordinates of the solution (write-only array).
 * @param func function being minimized passed as a pointer.
 * @param func.numargs size of the array x
 * @param func.whichFn, not used here. See cfsqp documentation for general use.
 * @param func.x, input variables of function
 * @param func.x, return value of function.
 * @param cFunc constraint function, passed as a pointer.
 * @param cFunc.numargs, size of the array x.
 * @param cFunc.whichFn, which constraint is being invoked 1,2,etc.
 * @param cFunc.x, variables of the constraint.
 * @param cFunc.ret, value of constaint,
 */ 

// find minimum, with equality constraint.
double findMinimumEQ(int numargs, int nconstr,
	double* xmin, double* xmax, double* x,
        void (*func)(int numargs,int whichFn,double* x,double* ret,void*),
        void (*cFunc)(int numargs,int which,double* x,double* ret,void*)) {

   int i,nparam,nf,nineq,neq,mode,iprint,miter,neqn,nineqn,
       ncsrl,ncsrn,nfsr,mesh_pts[1],inform;
   double bigbnd,eps,epsneq,udelta;
   double *f,*g,*lambda;
   double r[1]={0};
   void *cd;

   mode=100;    // C=1, B=0, A=0.
   iprint=0;    // print a little bit of stuff
   miter=2000;   // max number of iterations
   bigbnd=1.e10;  // a big number
   eps=1.e-8;     // a small number
   epsneq=0.e0;
   udelta=0.e0;
   nparam=numargs; // number of variables
   nf=1;			// number of objective functions
   nineq=nineqn=0; // number of nonlinear inequality constraints
   neqn=neq=nconstr;			// number of nonlinear equality constraints
   ncsrl=ncsrn=nfsr=mesh_pts[0]=0;
   f=(double *)calloc(nf,sizeof(double));
   g=(double *)calloc(nineq+neq,sizeof(double));
   lambda=(double *)calloc(nineq+neq+nf+nparam,sizeof(double));
	cd = NULL;
	// USE x as initial value.
	//	for (i=0;i<numargs;i++) x[i]=xmin[i]+(xmax[i]-xmin[i])*myrand();
	
   cfsqp(nparam,nf,nfsr,nineqn,nineq,neqn,neq,ncsrl,ncsrn,mesh_pts,
         mode,iprint,miter,&inform,bigbnd,eps,epsneq,udelta,xmin,xmax,x,
         f,g,lambda,func,cFunc,grobfd,grcnfd,cd);
   free(f);
   free(g);
   free(lambda);
   (*func)(numargs,1,x,r,cd);
	return r[0];
}
