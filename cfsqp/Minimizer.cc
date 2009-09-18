#include <iomanip.h>
#include <iostream.h>
#include <fstream.h>
#include <math.h>
#include <stdlib.h>
#include "float.h"
#include "Minimizer.h"

double minimize(int numargs, int nconstr,
	double* xmin, double* xmax, double* x,
        void (*func)(int numargs,int whichFn,double* x,double* ret,void*),
        void (*cFunc)(int numargs,int which,double* x,double* ret,void*));

/**
 * Invokes minimize repeatedly and takes the smallest case.
 * @param count times to invoke constrained_min, sample value=80
 * all other parameters are the same as in constrained_min.
 */

/* each constraint f is a nonpositivity constraint f <= 0 */

double repeatMinimize(int count, int numargs, int nconstr,
	double* xmin, double* xmax, double* x,
        void (*func)(int numargs,int whichFn,double* x,double* ret,void*),
        void (*cFunc) (int numargs,int which,double* x,double* ret,void*)
	) {
	double currentMin=DBL_MAX;
	double* y = new double[numargs];
	for (int i=0;i<numargs;i++) 
		x[i]=xmin[i];
	for (int i=0;i<count;i++) {
		double t = minimize(numargs,nconstr,xmin,xmax,y,func,cFunc);
		if (t<currentMin) {
			currentMin=t;
			for (int j=0;j<numargs;j++) x[j]=y[j];		
		}
	}
	delete y;
	return currentMin;
	}


Minimizer::Minimizer(int count, int numargs, int nconstr,
		double* xmin, double* xmax) {
	this->count = count;
	this->numargs = numargs;
	this->nconstr= nconstr;
	this->xmin = new double[numargs];
	this->xmax = new double[numargs];
	this->x = new double[numargs];
	this->cFunc = 0;
	this->func = 0;
	for (int i=0;i<numargs;i++) { 
		this->xmin[i]=this->x[i]=xmin[i]; 
		this->xmax[i]=xmax[i];
	}
}

double Minimizer::optimize(){
	return repeatMinimize(count,numargs,nconstr,
		xmin,xmax,x,func,cFunc);
}

void Minimizer::coutReport(char* s){
	cout << endl << endl;
	cout << "Cfsqp minimization results: " << s << endl;
	cout.precision(18);
	cout << "numargs = " << numargs << endl;
	double opt = optimize();
	cout << "constrained min: " << opt << endl;
	cout << "variables: " << "{";
	for (int i=0;i<numargs;i++) {
		cout << x[i] << (i+1<numargs ? ", ": "}") ;
		if ((i>0)&&(0==(i % 10))) cout << endl;
	}
        if (opt < 0.0) { cout << endl << "NEGATIVE!!"; }
	cout <<"\nExiting cfsqp numerical optimizer." << endl;	
}

