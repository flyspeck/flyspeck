#include <iomanip>
#include <iostream>
#include <fstream>
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
	std::cout << std::endl << std::endl;
	std::cout << "Cfsqp minimization results: " << s << std::endl;
	std::cout.precision(18);
	std::cout << "numargs = " << numargs << std::endl;
	double opt = optimize();
	std::cout << "constrained min: " << opt << std::endl;
	std::cout << "variables: " << "{";
	for (int i=0;i<numargs;i++) {
		std::cout << x[i] << (i+1<numargs ? ", ": "}") ;
		if ((i>0)&&(0==(i % 10))) std::cout << std::endl;
	}
        if (opt < 0.0) { std::cout << std::endl << "NEGATIVE!!"; }
	std::cout <<"\nExiting cfsqp numerical optimizer." << std::endl;	
}

