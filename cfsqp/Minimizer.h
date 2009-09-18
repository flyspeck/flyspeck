

/**
 * Minimizer contains the data for the minimization of one function
 * on a given domain, subject to a system of constraints.
 */
class Minimizer {
public:
	// lower endpoints of interval.
	double* xmin;

	// upper endpoints of interval.
	double* xmax;

	// numerically determined coordinates of minimum.
	double* x;

	/**
	 * count number of times to repeat minimization.
	 * numargs size of arrays xmin, xmax, x;
	 * nconstr number of constraints.
	 */
	int count,numargs,nconstr;

	/**
	 * func function to be minimized.
	 * cFunc constraints to be used.
	 */
	void (*func)(int numargs,int whichFn,double* x,double* ret,void*);
	void (*cFunc)(int numargs,int which,double* x,double* ret,void*);

	Minimizer(int count, int numargs, int nconstr, 
		double* xmin, double* xmax);

	// carries out the optimization of the data. Sets x and
	// returns the minimum value.
	double optimize();

	// calls optimize, and then outputs a report, printing message s.
	void coutReport(char* s);
};

