// nonlinear inequalities for linear programming relaxation.
// basic functions to be studied: azim, lnazim, sol (3), tau (3).

/* Thomas C. Hales
   file created June 17, 2009
   code to be used with cfsqp optimization.

 */

#include <iomanip.h>
#include <iostream.h>
#include <math.h>
#include "Minimizer.h"
#include "numerical.h"


// lp2009.cc
// $ make lp2009.o
// $ ./lp2009.o

// constructor calls optimizer.  No need to place in main loop.
class trialdata {
public:
  trialdata(Minimizer M,char* s) {
    M.coutReport(s);
  };
};

int trialcount = 80;
double eps = 1.0e-6;

