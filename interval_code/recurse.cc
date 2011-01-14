/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                            */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                     */
/* ========================================================================== */

//  copyright (c) 1997, Thomas C. Hales, all rights reserved.


#include <iomanip>
#include <float.h>

//#include <iostream.h>
extern "C"
{
#include <math.h>
#include <time.h>
//#include <stdlib.h>
}
#include "error.h"
#include "interval.h"
#include "secondDerive.h"
#include "taylorInterval.h"
#include "recurse.h"
#include "../cfsqp/2065952723A.h"   // custom case.
using namespace std;

static const int MAXcount = 6; // MAX number of taylorFunctions in an array.

static const int DIM6 = 6; // number of variables in inequalities.  This is not resettable.
/*
static inline double dabs(interval x)
	{
	return interMath::sup(interMath::max(x,-x));	
	}
*/
static double max(const double x[DIM6])
	{
	double t=x[0];
	for (int j=0;j<DIM6;j++) if (x[j]>t) t = x[j];
	return t;
	}

static double max(double x,double y)
	{
	return x > y ? x : y;
	}

static double min(double x,double y)
	{
	return y > x ? x : y;
	}

static void centerform
	(const double x[DIM6],const double z[DIM6],double y[DIM6],double w[DIM6])
	{ // y = center of Taylor expansion = approximate center.
	interMath::up();
	for (int j=0;j<DIM6;j++)
		{
		y[j]= (z[j]+x[j])/2.0;
		w[j]= max(z[j]-y[j],y[j]-x[j]); //up-mode required.
		}
	}

/*
static int unreduced(const double x[DIM6],const double z[DIM6])
	{
	int t;
	t = (
		   ((z[0]==x[0])&&(z[3]==x[3])) 
		|| ((z[1]==x[1])&&(z[4]==x[4]))
		|| ((z[2]==x[2])&&(z[5]==x[5]))
		|| ((z[3]==x[3])&&(z[4]==x[4]))
		|| ((z[3]==x[3])&&(z[5]==x[5]))
		|| ((z[4]==x[4])&&(z[5]==x[5]))
		|| ((z[0]==x[0])&&(z[1]==x[1])&&(z[2]==x[2]))
	     );
	return (!t);
	}
*/

/*
static int setreduction(int i,const double x[DIM6],const double z[DIM6],
	const double x0[DIM6], double zz[DIM6])
	// return false if the reduction flows out of the cell.
	// else true;
	{
	for (int j=0;j<DIM6;j++) zz[j]=z[j];
	switch (i)
		{
		case 0 : if ((x[0]>x0[0])||(x[3]>x0[3])) return 0; 
			 zz[0]=x[0]; zz[3]=x[3];
			 break;
		case 1 : if ((x[1]>x0[1])||(x[4]>x0[4])) return 0; 
			 zz[1]=x[1]; zz[4]=x[4];
			 break;
		case 2 : if ((x[2]>x0[2])||(x[5]>x0[5])) return 0; 
			 zz[2]=x[2]; zz[5]=x[5];
			 break;
		case 3 : if ((x[3]>x0[3])||(x[4]>x0[4])) return 0; 
			 zz[3]=x[3]; zz[4]=x[4];
			 break;
		case 4 : if ((x[3]>x0[3])||(x[5]>x0[5])) return 0; 
			 zz[3]=x[3]; zz[5]=x[5];
			 break;
		case 5 : if ((x[4]>x0[4])||(x[5]>x0[5])) return 0; 
			 zz[4]=x[4]; zz[5]=x[5];
			 break;
		case 6 : if ((x[0]>x0[0])||(x[1]>x0[1])||(x[2]>x0[2])) 
			 return 0; 
			 zz[0]=x[0]; zz[1]=x[1]; zz[2]=x[2];
			 break;
		default : error::message("setreduction out of range");
		}
	return 1;
	}
*/


/*
static int reducible(const taylorFunction* I[],int count)
	{
	for (int i=0;i<count;i++)
		if (!I[i]->getReducibleState()) return 0;
	return 1;
	}
*/

static void report_failure(const double x[DIM6],const double z[DIM6],const char* s)
	{
	static const int MAXFAIL=25;
	static int fail_count=0;
	cout.precision(20);
	interMath::down();
	cout << "\n{" << flush;
	for (int j=0;j<DIM6;j++) cout << x[j] << (j+1<DIM6?",":"} ")  << flush;
	interMath::up();
	cout << "{" << flush;
	for (int j=0;j<DIM6;j++) cout << z[j] << (j+1<DIM6?",":"} ")  << flush;
	cout << " " << flush;
	cout << s << endl << flush;
	if (fail_count++> MAXFAIL)
		{ error::message("too many exceptions; bailing out");
		  exit(0);
		}
	cout << flush;
	}

static double deltainf(double x1,double x2,double x3,double x4,double x5,
        double x6)
        {
        interMath::down();
        return
         ((-x2)*x3)*x4 +((- x1)*x3)*x5 +((- x1)*x2)*x6 +((- x4)*x5)*x6 +
   x3*(x1 + x2 + x4 + x5)*x6 +  (x3*(-x3-x6))*x6 +
   x2*x5*(x1 + x3 + x4 + x6) + x2*(x5*(-x2-x5)) +
        x1*x4*(x2 + x3 + x5 + x6)+ x1*(x4*(-x1-x4));
        }

static inline int sgn(interval x) 
{ if (interMath::inf(x)>0.0) return 1;
  else if (interMath::sup(x)<0.0) return -1; else return 0;
}

static int sameSgn(const lineInterval& x,const lineInterval& y)
{
  for (int j=0;j<DIM6;j++) if (sgn(x.partial(j))!=sgn(y.partial(j))) return 0;
  return 1;
}

static void resetBoundary(double x0[DIM6],double z0[DIM6],
			  const double x[DIM6],const double z[DIM6])
{
  for (int j=0;j<DIM6;j++) { x0[j]=x[j]; z0[j]=z[j]; }
}

static void deleteFunction(const taylorInterval* T[],const taylorFunction* I[],
			   int& count,int k)
{
  count--; if (count<0) error::message("unexpected negative number");
  for (int i=k;i<count;i++)
    { T[i]=T[i+1];  I[i]=I[i+1]; }
}

// to be used when reducing to a single inequality.  We overwrite at 0.
static void moveFirst(const taylorInterval* T[],const taylorFunction* I[],int k)
{
  if (k>0) { T[0]=T[k];  I[0]=I[k]; }
}

static cellOption::cellStatus verifyCell(double x[DIM6],double z[DIM6],
					 double x0[DIM6],double z0[DIM6],
		const taylorFunction* I[],int& count,
		cellOption opt)	{

  if (count>MAXcount) {
    cout << "There are " << count << " inequalities." << endl;
    error::fatal("In verifyCell, increase MAXcount and recompile");
    return cellOption::inconclusive;
  }

  if (opt.onlyCheckDeriv1Negative) {
    if (
	//opt.isUsingDihMax() || opt.isUsingBigFace126() || 
	(count > 1)) {
      error::fatal("verifyCell: incompatible opt");
    }
  }

  /* use "rad2" to compute lower and upper bounds on x4 */ {
    if (opt.setRad2) {
      try {
	double x4max = edgeBound::x4_upper_from_rad2(x);
	if (x4max < x[3]) return cellOption::cellPasses;
	if (x4max < z[3]) { z[3] = x4max;  }} catch (unstable x) { }
      try {
	double x4min = edgeBound::x4_lower_from_rad2(z);
	if (x4min > z[3]) return cellOption::cellPasses;
	if (x4min > x[3]) { x[3] = x4min;  }} catch (unstable x) {} 
    }
  }

  /* use delta126, delta135 to computer  bounds on edges */ {
    if (opt. delta126Min > -1.0) {
      try { double x6max = edgeBound::x3_upper_from_delta(opt.delta126Min,x[0],x[1]);
	if (x6max < x[5]) return cellOption::cellPasses;
	if (x6max < z[5]) { z[5] = x6max; } } catch (unstable x) {}
    }
    if (opt.delta126Max > -1.0) {
      try { double x6min = edgeBound::x3_lower_from_delta(opt.delta126Max,z[0],z[1]);
	if (x6min > z[5]) return cellOption::cellPasses;
	if (x6min > x[5]) { x[5] = x6min; } } catch (unstable x) {}
    }
    if (opt. delta135Min > -1.0) {
      try { double x5max = edgeBound::x3_upper_from_delta(opt.delta135Min,x[0],x[2]);
	if (x5max < x[4]) return cellOption::cellPasses;
	if (x5max < z[4]) { z[4] = x5max; } } catch (unstable x) {}
    }
    if (opt.delta135Max > -1.0) {
      try { double x5min = edgeBound::x3_lower_from_delta(opt.delta135Max,z[0],z[2]);
	if (x5min > z[4]) return cellOption::cellPasses;
	if (x5min > x[4]) { x[4] = x5min; } } catch (unstable x) {}
    }
  }

  static const double WCUTOFF = 0.05;

  /* GOING STRONG LOOP*/
  const taylorInterval* T[MAXcount];
  taylorInterval  Target[MAXcount];
  int goingstrong=1;
  double maxwidth=1.0;
  while (goingstrong--)
    {
      
      /* calculate width */ {
	double y[DIM6],w[DIM6];
	centerform(x,z,y,w); 
	maxwidth = max(w); 
      }

      /*pass cell if some taylor bound holds*/{
	int has_unstable_branch=0;
	int i=0; while (i<count)     { // each loop increments i, or decrements count.
	  try { Target[i]= I[i]->evalf(domain(x),domain(z));   
	    taylorInterval* U=&Target[i]; 
	    if (opt.onlyCheckDeriv1Negative) {
	      if (U->upperPartial(0)<0.0) { return cellOption::cellPasses; }
	      if (U->lowerPartial(0)>0.0) { return cellOption::counterexample; }
	      return cellOption::inconclusive;
	    }
	    if (U->upperBound()<0.0) return cellOption::cellPasses;
	    T[i] = &Target[i];
	    i++;
	  }
	  // exceptions are common early on, when intervals are too fat for reliable computation:
	  catch (unstable u) { // modified Jan 14, 2011.
	    if (2.0 * maxwidth > WCUTOFF) {
	      has_unstable_branch=1;  
	      i++;
	    }
	    else {
	      resetBoundary(x0,z0,x,z);
	      deleteFunction(T,I,count,i); //decrements count; T not initialized, but no matter.
	    }
	  } // end unstable. 
	} // end while
	if (has_unstable_branch) { return cellOption::inconclusive; }
      }
      
      /*report zero width cells */ {
	static const double epsilon_width = 1.0e-8;
	if (maxwidth < epsilon_width) 
	  {
	    if (opt.getPrintMode()==cellOption::silent) 
	      return cellOption::counterexample; 
	    report_failure(x,z,"isolated point");
	    cout.precision(20);
	    for (int i=0;i<count;i++)
	      {
		interMath::down();
		cout << "  value=[" << T[i]->lowerBound() << flush;
		interMath::up();
		cout << "," << T[i]->upperBound() << "]\n" << flush;
		for (int j=0;j<DIM6;j++) 
		  { cout << "T" << i << " partial " << j << 
		      ": [" << (T[i]->lowerPartial(j)) << 
		      "," << (T[i]->upperPartial(j)) << "]\n" << flush;
		  }
	      }
	    cout << flush;
	    (opt.allowSharp ? error::inc_corner(): error::message("corner solution failure "));   
	    return (opt.allowSharp ? cellOption::cellPasses : cellOption::counterexample);
	  }
      }
      
      /*delete false inequalities */{
	int i=0; while (i<count)
		   {
		     if (T[i]->lowerBound() > 0.0)
		       {
			 resetBoundary(x0,z0,x,z);
			 deleteFunction(T,I,count,i); //it decrements count; 
		       }
		     else i++;
		   }
	if (count==0) 
	  {
	    if (opt.getPrintMode()==cellOption::silent) 
	      return cellOption::counterexample; 
	    report_failure(x,z,"current inequalities are false");
	    return cellOption::counterexample;
	  }
      }
      
      /* do derivatives. */{
	for (int j=0;j<DIM6;j++) if (x[j]<z[j]) {
	    int allpos=1, allneg=1;
	    for (int i=0;i<count;i++) if (T[i]->lowerPartial(j)<0.0) allpos=0;
	    for (int i=0;i<count;i++) if (T[i]->upperPartial(j)>= 0.0) allneg=0; // >= breaks symmetry.
	    if (allpos)
	      {
		if (z[j]<z0[j]) return cellOption::cellPasses; // slide off the edge.
		else { z0[j]=x0[j]=x[j]=z[j]; goingstrong=1; }
	      }
	    else if (allneg)
	      {
		if (x[j]>x0[j]) return cellOption::cellPasses;
		else { x0[j]=z0[j]=z[j]=x[j]; goingstrong=1; }
	      }
	  }
      }
      
    } // end while goingstrong
  
  
  // now drop the numerically false inequalities;
  int mixedsign;
  double yyn[DIM6],yu[DIM6];  // look at the lowest & highest corners
  lineInterval cn,cu;
  if (maxwidth<WCUTOFF)
    {
      int i=0; 
      while (i<count) if (T[i]->tangentVectorOf().low() >0.0)  {
	  mixedsign=0;
	  for (int j=0;j<DIM6;j++)
	    {
	      yyn[j]= (sgn(T[i]->tangentVectorOf().partial(j)) >0 ? x[j] : z[j]);
	      yu[j]= (sgn(T[i]->tangentVectorOf().partial(j))> 0 ? z[j] : x[j]);
	      if (sgn(T[i]->tangentVectorOf().partial(j))==0) mixedsign = 1;
	    }
	  if (mixedsign) { mixedsign=0; i++; continue; }
	  cn = I[i]->tangentAtEstimate(domain(yyn)); 
	  cu= I[i]->tangentAtEstimate(domain(yu));
	  if ((min(cn.low(),cu.low())>0.0)&&
	      (sameSgn(T[i]->tangentVectorOf(),cn))&&
	      sameSgn(T[i]->tangentVectorOf(),cu))
	    {
	      deleteFunction(T,I,count,i); 
	      resetBoundary(x0,z0,x,z);
	    }
	  else i++;
	}
	else i++;
    }
  if (count==0) 
    {
      if (opt.getPrintMode()==cellOption::silent) return cellOption::counterexample; 
      report_failure(x,z,"current inequalities are doubtful");
      return cellOption::counterexample;
    }
  
  // now keep a single numerically true inequality.
  if ((maxwidth<WCUTOFF)&&(count>1))
    {
      double margin =0.0;
      for (int i=0;i<count;i++) if (T[i]->tangentVectorOf().hi()< 0.0)
				  {
				    mixedsign=0;
				    for (int j=0;j<DIM6;j++)
				      {
					yyn[j]= (sgn(T[i]->tangentVectorOf().partial(j))>0 ? x[j] : z[j]);
					yu[j]= (sgn(T[i]->tangentVectorOf().partial(j))>0 ? z[j] : x[j]);
					if (sgn(T[i]->tangentVectorOf().partial(j))) mixedsign= 1;
				      }
				    if (mixedsign) { mixedsign=0; continue; }
				    cn = I[i]->tangentAtEstimate(domain(yyn)); cu= I[i]->tangentAtEstimate(domain(yu));
				    if ((max(cn.hi(),cu.hi())< -margin)&&
					(sameSgn(T[i]->tangentVectorOf(),cn))&&sameSgn(T[i]->tangentVectorOf(),cu))
				      {
					margin = -max(cn.hi(),cu.hi());
					if (i) 
					  {
					    moveFirst(T,I,i);
					    resetBoundary(x0,z0,x,z);
					  }
				      }
				  }
      if (margin>0.0) count =1; // Disregard the rest of the inequalities;
    } // if maxwidth
  return cellOption::inconclusive;
} // end verifyCell.

static int count(int i,int j)
{
  return (0 == (i % j));
}

static long timeout = 0; //  Set with options.  opt.Time out after this many seconds.

void stats(int force) {
  static const long starting_time = time(0); //  Time out after this many seconds.
  
  static int statcounter=0;
  static int linefeed=0;
  if (force) { cout << "[cellcount:" << statcounter << "]" << endl << flush; }
  if (time(0) - starting_time > timeout) {
    char msg[100];
    sprintf(msg, "time allocation exceeded %dK secs. Bailing out.", (timeout / 1000));
    error::fatal(msg);
  }
  else if (count(statcounter++,10000)) 
    {
      if (count(linefeed++,10) )
	{
	  cout << " " << flush; 
	  error::printTime();	  
	}
      /*  206A case only. */ {
      int c = getCounter();  
      if (c>0) { cout << "(" << getCounter() << ":" << percent_done() << ")"; }
      }
      cout << "[" << statcounter/10000 << "*10^4]" << flush;
    }
}

int prove::recursiveVerifier(int depth,
			     const domain& xD,const domain& zD,     /// current cell
			     const domain& x0D,const domain& z0D,   // boundary
			     const taylorFunction* I[],
			     int count,cellOption& options)
// function should not change any of these parameters.
// except iterationCount in options.
{
  double x[DIM6],z[DIM6];     /// current cell
  double x0[DIM6],z0[DIM6]; 
  for (int j=0;j<DIM6;j++)
    {
      x[j]=xD.getValue(j); z[j]=zD.getValue(j);
      x0[j]=x0D.getValue(j); z0[j]=z0D.getValue(j);
    }
  timeout = options.timeout;
  stats(0); 
  if (depth==0) { set_rectangle(x,z); }  // 206A code.
  options.augmentIterationCount();
  if ((options.getIterationLimit()>0)&&
      (options.getIterationLimit()<options.getIterationCount()))
    {
      report_failure(x,z,"iteration limit exceeded");
      cout << "iteration limit is set at " << options.getIterationLimit() << endl;
      stats(1);
      return 0;
    }
  
  /* exit if too deep */ {
    int MAXDEPTH = 200;
    if (options.getRecursionDepth()>0) MAXDEPTH = options.getRecursionDepth();
    if (depth > MAXDEPTH) 
      {
	report_failure(x,z,"recursion limit exceeded");
	cout << "recursion depth is currently at " << MAXDEPTH << endl;
	cout << "count = " << count << endl;
	for (int i=0;i<count;i++) {
	  taylorInterval T0= I[i]->evalf(domain(x),domain(z)); 
	  taylorInterval* T=&T0;
	  cout << "lower " << i << " " << T->lowerBound() << endl;
	  cout << "upper " << i << " " << T->upperBound() << endl;
	}
	return 0;
      }
  }
  
  // make a backup. verifyCell changes the parameters.
  double xx[DIM6],zz[DIM6],xx0[DIM6],zz0[DIM6];
  for (int j=0;j<DIM6;j++) 
    {xx[j]=x[j];zz[j]=z[j];xx0[j]=x0[j];zz0[j]=z0[j];}
  if (count>MAXcount) 
    {
      cout << "There are " << count << " inequalities in use."
	   << endl << flush;
      error::message("Change the parameter MAXcount and recompile");
      return 0;
    }
  const taylorFunction* II[MAXcount];
  for (int i=0;i<count;i++) II[i]=I[i]; 
  int Ncount = count;

  /* special code for one difficult inequality */ 
  if (options.strategy206A) {
    strategy s;
    setStrategy206A(xx,zz,s);
    if (!(s.mode == strategy::split)) {
	  static interval one("1");
	  interval alpha(s.alpha,s.alpha);
	  interval malpha = one - interMath::max(alpha,-alpha);
	  const taylorFunction F = 
	    ( (s.mode==strategy::n1) ? taylorSimplex::num1   :
	      ((s.mode ==strategy::n1m) ? taylorSimplex::num1 * "- 1"  :
	       ((s.mode == strategy::n2m) ? taylorSimplex::num2 * " - 1" :
		(assert(s.mode == strategy::merge),
                taylorSimplex::num2 * malpha * "-1" + 
		 taylorSimplex::num1 * alpha) ) ) );
	  const taylorFunction Fm = F * "-1";
	  const taylorFunction* J[1] = {&Fm};
	  // use linearity in e1,e2,e3 to do dimension reduction.
	  for (int i=0;i<2;i++) for (int j=0;j<2;j++) for (int k=0;k<2;k++) {
		double xr[6], zr[6];
		xr[0] = (i ? zz[0] : xx[0]); zr[0] = xr[0];
		xr[1] = (j ? zz[1] : xx[1]); zr[1] = xr[1];
		xr[2] = (k ? zz[2] : xx[2]); zr[2] = xr[2];
		for (int r=3;r<6;r++) { xr[r]=xx[r]; zr[r] = zz[r]; }
		cellOption opt1;
		opt1.setPrintMode(cellOption::silent);
		opt1.iterationCount = options.iterationCount;
		int rv = recursiveVerifier(depth+1,xr,zr,xr,zr,J,1,opt1);
		options.iterationCount   = opt1.iterationCount;
		if (!rv) {
		  cout << " i j k d " << i << " " << j << " " << k << " " << depth << endl;
		  cout << "x r" << endl;
		  for (int u=0;u<6;u++) {
		    cout << xr[u] << " " << zr[u] << endl;
		  }
		  if (s.mode==strategy::merge) 
		    { cout << " alpha " << alpha << endl; }
		  return 0;

		}
	      }
	  return 1;
    }
  }


  else {
  /* Here is the main line of the procedure.  Check if it verifies. */
  cellOption::cellStatus  v =verifyCell(xx,zz,xx0,zz0,II,Ncount,
				       options);// xx,zz,xx0,zz0,II,Ncount .. affected.
  if (v==cellOption::counterexample) {
    cout << "counterexample found " << endl;
    return 0; 
  }
  else if (v==cellOption::cellPasses) { return 1;  }
  assert (v==cellOption::inconclusive);
  }
  /* run recursion into two cases. */ { 
    interMath::up();
    int j_wide=0; /* init j_wide */ {
      double w = zz[0]-xx[0]; 
      for (int j=0;j<DIM6;j++) {
	if (zz[j]-xx[j] > w) { j_wide = j; w = zz[j]-xx[j]; }
      }}
    for (int k=0;k<2;k++) 	{
      double y, xr[DIM6], zr[DIM6];
      y = (xx[j_wide]+zz[j_wide])/2.0;
      for (int j=0;j<DIM6;j++) { xr[j] = xx[j]; zr[j]=zz[j]; }
      (k? xr[j_wide] = y : zr[j_wide] = y);
      if (!recursiveVerifier(depth+1,xr,zr,xx0,zz0,II,Ncount,
			     options)) return 0;
    }}
  if (depth==0) { stats(1); }
  return 1;
}





/**********************************************

				START of QUAD CLUSTER MATERIAL 

***********************************************/

static int fitstogether(const double x[6],const double y[6])
{
  return ((x[1]==y[1])&&(x[2]==y[2])&&(x[3]==y[3]));
}

/*
  static int unreducedQ(const double xA[6],const double xB[6],
  const double zA[6],const double zB[6])
  {
  int t;
  t = (
  ((zA[4]==xA[4])&&(zB[5]==xB[5])) 
  || ((zA[5]==xA[5])&&(zB[4]==xB[4]))
  || ((zA[4]==xA[4])&&(zB[4]==xB[4])&&(zA[1]==xA[1]))
  || ((zA[5]==xA[5])&&(zB[5]==xB[5])&&(zA[2]==xA[2]))
  || ((zA[4]==xA[4])&&(zA[5]==xA[5])&&(zB[0]==xB[0]))
  || ((zB[4]==xB[4])&&(zB[5]==xB[5])&&(zA[0]==xA[0]))
  || ((zA[0]==xA[0])&&(zA[1]==xA[1])&&(zB[4]==xB[4]))
  || ((zA[0]==xA[0])&&(zA[2]==xA[2])&&(zB[5]==xB[5]))
  || ((zB[0]==xB[0])&&(zB[2]==xB[2])&&(zA[5]==xA[5]))
  || ((zB[0]==xB[0])&&(zB[1]==xB[1])&&(zA[4]==xA[4]))
  || ((zB[0]==xB[0])&&(zB[1]==xB[1])&&(zB[2]==xB[2])&&
  (zA[0]==xA[0])) // case 10
  || ((zA[4]==xA[4])&&(zB[4]==xB[4])&&(zB[3]==xB[3]))
  || ((zA[5]==xA[5])&&(zB[5]==xB[5])&&(zB[3]==xB[3])) //12
  || ((zB[3]==xB[3])&&(zB[0]==xB[0])&&(zA[4]==xA[4])) //13
  || ((zB[3]==xB[3])&&(zB[0]==xB[0])&&(zA[5]==xA[5])) //14
  || ((zB[3]==xB[3])&&(zA[0]==xA[0])&&(zB[4]==xB[4])) //15
  || ((zB[3]==xB[3])&&(zA[0]==xA[0])&&(zB[5]==xB[5])) //16
  || ((zB[3]==xB[3])&&(zA[0]==xA[0])&&(zB[0]==xB[0])) //17
  );
  return (!t);
  }
*/

/*
  static int setreductionQ(int i,const double xA[6],const double xB[6],
  const double zA[6],const double zB[6],
  double zzA[6],double zzB[6])
  // return false if the reduction flows out of the cell.
  // else true;
  {
  int j;
  for (j=0;j<6;j++) { zzA[j]=zA[j]; zzB[j]=zB[j]; }
  switch (i)
  {
  case 0 : zzA[4]=xA[4]; zzB[5]=xB[5]; break;
  case 1 : zzA[1]=zzB[1]=xA[1]; zzA[4]=xA[4]; zzB[4]=xB[4]; break;
  case 2 : zzA[4]=xA[4]; zzA[5]=xA[5]; zzB[0]=xB[0]; break;
  case 3 : zzA[0]=xA[0]; zzB[4]=xB[4]; zzB[5]=xB[5]; break;
  case 4 : zzA[0]=xA[0]; zzA[1]=zzB[1]=xA[1]; zzB[4]=xB[4]; break;
  case 5 : zzA[1]=zzB[1]=xA[1]; zzA[4]=xA[4]; zzB[0]=xB[0]; break;
  case 6 : zzA[0]=xA[0]; zzA[1]=zzB[1]=xA[1]; 
  zzA[2]=zzB[2]=xA[2]; zzB[0]=xB[0]; break;
  case 7 : zzA[5]=xA[5]; zzB[4]=xB[4]; break;
  case 8 : zzA[2]=zzB[2]=xA[2]; zzA[5]=xA[5]; zzB[5]=xB[5]; break;
  case 9 : zzA[0]=xA[0]; zzA[2]=zzB[2]=xA[2]; zzB[5]=xB[5]; break;
  case 10: zzA[2]=zzB[2]=xA[2]; zzA[5]=xA[5]; zzB[0]=xB[0]; break;
  case 11: zzA[3]=zzB[3]=xA[3]; zzA[4]=xA[4]; zzB[4]=xB[4]; break;
  case 12: zzA[3]=zzB[3]=xA[3]; zzA[5]=xA[5]; zzB[5]=xB[5]; break;
  case 13: zzA[3]=zzB[3]=xA[3]; zzA[4]=xA[4]; zzB[0]=xB[0]; break;
  case 14: zzA[3]=zzB[3]=xA[3]; zzA[5]=xA[5]; zzB[0]=xB[0]; break;
  case 15: zzA[3]=zzB[3]=xA[3]; zzA[0]=xA[0]; zzB[4]=xB[4]; break;
  case 16: zzA[3]=zzB[3]=xA[3]; zzA[0]=xA[0]; zzB[5]=xB[5]; break;
  case 17: zzA[3]=zzB[3]=xA[3]; zzA[0]=xA[0]; zzB[0]=xB[0]; break;
  default : error::message("setreductionQ out of range");
  }
  return 1;
  }
*/

static void setDimRedBackSym(int i /* 0..7 */ ,const double xA[6],const double xB[6],
			     const double zA[6],const double zB[6],
			     double xxA[6],double xxB[6],double zzA[6],double zzB[6])
{
  for (int j=0;j<6;j++) { zzA[j]=zA[j]; zzB[j]=zB[j]; xxA[j]= xA[j]; xxB[j]= xB[j];  }
  switch (i % 2)
    {
    case 0 : zzA[0]=xA[0]; xxA[0]=xA[0]; break;
    case 1 : zzA[4]=xA[4];  xxA[4]=xA[4]; break;
    default : error::fatal("setDimRedBackSym A variable out of range");
    }
  switch (i / 2) 
    {
    case 0 : 
      zzB[4]=xB[4]; xxB[4]=xB[4]; 
      zzB[5]=xB[5]; xxB[5]=xB[5]; 
      break;
    case 1:
      zzB[4]=zB[4]; xxB[4]=zB[4]; 
      zzB[5]=xB[5]; xxB[5]=xB[5]; 
      break;
    case 2 : 
      zzB[4]=xB[4]; xxB[4]=xB[4]; 
      zzB[5]=zB[5]; xxB[5]=zB[5]; 
      break;
    case 3:
      zzB[0]=xB[0]; zzB[0]=xB[0];
      zzB[4]=zB[4]; xxB[4]=zB[4]; 
      zzB[5]=zB[5]; xxB[5]=zB[5]; 
      break;
    default : error::fatal("setDimRedBackSym B variable out of range");
    }
}

static int sameSgnQ(const lineInterval& cA,const lineInterval& cB,
		    const lineInterval& dA,const lineInterval& dB)
{
  int k[3]={0,4,5},i;
  for (i=0;i<3;i++) 
    if (sgn(cA.partial(k[i]))!=sgn(dA.partial(k[i]))) return 0;
  for (i=0;i<3;i++) 
    if (sgn(cB.partial(k[i]))!=sgn(dB.partial(k[i]))) return 0;
  for (i=1;i<4;i++) 
    if (sgn(cA.partial(i)+cB.partial(i))!=
	sgn(dA.partial(i)+dB.partial(i))) return 0;
  return 1;
}

static void deleteIneqQ(const taylorInterval* tA[],const taylorInterval* tB[],
			const taylorFunction* IA[],const taylorFunction* IB[],int& Nineq,int i)
{
  Nineq--; if (Nineq<0) error::message("unexpected negative numberQ");
  int j;
  for (j=i;j<Nineq;j++)
    { tA[j]=tA[j+1];  IA[j]=IA[j+1]; 
      tB[j]=tB[j+1];  IB[j]=IB[j+1]; }
}

static void printit(const double x[6])
{
  cout.precision(8); interMath::nearest();
  for (int i=0;i<6;i++) cout << x[i] << " " << flush;
  cout << endl << flush;
}

static int verifyCellQ(double xA[6],double xB[6],double zA[6],double zB[6],
		       const taylorFunction* IA[],const taylorFunction* IB[],
		       int& Nineq,cellOption& option)
// return true if all verifies or if all counterexamples have been
// 	properly reported.
//return false if x,z ... require further investigation.
{
  
  // check preconditions.
  if (!fitstogether(xA,xB))
    {
      error::message("Qx-mismatch"); printit(xA); printit(xB); return 0;
    }
  if (!fitstogether(zA,zB))
    {
      error::message("Qz-mismatch"); printit(zA); printit(zB); return 0;
    }
  
  // get out if delta is possibly negative.
  if (deltainf(zA[0],xA[1],xA[2],zA[3],xA[4],xA[5])<=0.0) return 0;
  if (deltainf(zB[0],xB[1],xB[2],zB[3],xB[4],xB[5])<=0.0) return 0;
  
  // initialize
  double yA[6],yB[6],wA[6],wB[6]; 
  const taylorInterval* tA[MAXcount];
  const taylorInterval* tB[MAXcount]; 
  taylorInterval targetA[MAXcount];
  taylorInterval targetB[MAXcount];
  if (Nineq>MAXcount) 
    {
      cout << "There are " << Nineq << " inequalities." << endl;
      error::message("Update MAXcount in verifyCellQ");
      return 0;
    }
  
  /* get out fast if any of the crude taylor bounds hold. */ {
    int unstable_data = 0;
    for (int i=0;i<Nineq;i++)
      {
	try {
	  targetA[i]= IA[i]->evalf(xA,zA); 
	  tA[i]=&targetA[i];
	  targetB[i]= IB[i]->evalf(xB,zB); 
	  tB[i]=&targetB[i];
	  if (taylorInterval::upperboundQ(*tA[i],*tB[i])< 0.0) return 1;
	}
	catch (unstable x) { unstable_data = 1; }
      }
    if (unstable_data) return 0;
  }
  
  centerform(xA,zA,yA,wA); 
  centerform(xB,zB,yB,wB); 
  
  /* fail if interval has width epsilon */ {
    static const double epsilon_width = 1.0e-8;
    if (max(max(wA),max(wB)) < epsilon_width) 
      {
	report_failure(xA,zA,"A:isolated point");
	report_failure(xB,zB,"B:isolated point");
	cout.precision(20);
	for (int i=0;i<Nineq;i++)
	  {
	    interMath::down();
	    cout << "  value=[A:" << tA[i]->lowerBound() << flush;
	    interMath::up();
	    cout << "," << tA[i]->upperBound() << "]" << flush;
	    interMath::down();
	    cout << "  [B:" << tB[i]->lowerBound()  << flush;
	    interMath::up();
	    cout << "," << tB[i]->upperBound() << "]\n" << flush;
	  }
	cout << flush;
	error::fatal("isolated point failure");
      }
  }
  
  /* delete false ineqs */ {
    int i=0; while (i<Nineq)
	       {
		 if (taylorInterval::lowerboundQ(*tA[i],*tB[i]) > 0.0)
		   {
		     deleteIneqQ(tA,tB,IA,IB,Nineq,i); 
		     //it decrements Nineq; 
		   }
		 else i++;
	       }
    if (Nineq==0) 
      {
	report_failure(xA,zA,"A:current inequalities are false");
	report_failure(xB,zB,"B:current inequalities are false");
	error::fatal("no true inequalities");
      }
  }
  if (Nineq==1) return 0;
  
  // now keep a single numerically true inequality.
  double WCUTOFF = 0.3;
  if (max(zA[0],zB[0])>6.00) WCUTOFF=0.1; // heuristic: things are unstable here!
  if (option.hasWidthCutoff()) WCUTOFF=option.getWidthCutoff(); 
  int s;
  if ((max(max(wA),max(wB))<WCUTOFF)&&(Nineq>1))
    {
      double yAn[6],yAu[6],yBn[6],yBu[6];
      // look at the lowest & highest corners
      int k[3]={0,4,5};
      lineInterval tAn,tAu,tBn,tBu;
      int mixedsign;
      double margin =0.0;
      for (int i=0;i<Nineq;i++) 
	if (interMath::up(), tA[i]->tangentVectorOf().hi()+tB[i]->tangentVectorOf().hi()< 0.0)
	  {
	    mixedsign=0;
	    for (int j=0;j<3;j++)
	      {
		s = sgn(tA[i]->tangentVectorOf().partial(k[j]));
		yAn[k[j]]= (s>0 ? xA[k[j]]: zA[k[j]]);
		yAu[k[j]]= (s>0 ? zA[k[j]]: xA[k[j]]);
		if (s==0) mixedsign= 1;
	      }
	    if (mixedsign) { mixedsign=0; continue; }
	    for (int j=0;j<3;j++)
	      {
		s = sgn(tB[i]->tangentVectorOf().partial(k[j]));
		yBn[k[j]]= (s>0 ? xB[k[j]]: zB[k[j]]);
		yBu[k[j]]= (s>0 ? zB[k[j]]: xB[k[j]]);
		if (s==0) mixedsign= 1;
	      }
	    if (mixedsign) { mixedsign=0; continue; }
	    for (int j=1;j<4;j++)
	      {
		s = sgn(tB[i]->tangentVectorOf().partial(j)
			+tA[i]->tangentVectorOf().partial(j));
		yAn[j]=yBn[j]= (s>0 ? xB[j]: zB[j]);
		yAu[j]=yBu[j]= (s>0 ? zB[j]: xB[j]);
		if (s==0) mixedsign= 1;
	      }
	    if (mixedsign) { mixedsign=0; continue; }
	    tAn = IA[i]->tangentAtEstimate(yAn); tAu= IA[i]->tangentAtEstimate(yAu);
	    tBn = IB[i]->tangentAtEstimate(yBn); tBu= IB[i]->tangentAtEstimate(yBu);
	    double temp_margin = min(-tAn.hi()-tBn.hi(),-tAu.hi()-tBu.hi());
	    if ((temp_margin > margin)
		&&(sameSgnQ(tA[i]->tangentVectorOf(),tB[i]->tangentVectorOf(),tAn,tBn))
		&&(sameSgnQ(tA[i]->tangentVectorOf(),tB[i]->tangentVectorOf(),tAu,tBu)))
	      {
		margin = temp_margin;
		moveFirst(tA,IA,i);
		moveFirst(tB,IB,i);
	      }
	  }
      static double margin_lowerbound = 0.0000;
      if (margin>margin_lowerbound) Nineq =1; // Disregard the rest of the inequalities;
    } // if max(w) 
  return 0;
} // end verifyCellQ.



static int breaksapart(int depth, // all inputs are left unchanged.
		       const double xA[6],const double xB[6],
		       const double zA[6],const double zB[6],
		       const taylorFunction* IA[],const taylorFunction* IB[],int Nineq,double margin)
{
  static const interval zero("0");
  static const interval two("2");
  if (Nineq<1) { error::fatal("No inequalities"); }
  if (Nineq>1) return 0;
  if (deltainf(zA[0],xA[1],xA[2],zA[3],xA[4],xA[5])<= 0.5) return 0;
  if (deltainf(zB[0],xB[1],xB[2],zB[3],xB[4],xB[5])<=0.5) return 0;
  
  double yA[6],yB[6],wA[6],wB[6];
  lineInterval tA,tB;
  /* initialize center */ {
    centerform(xA,zA,yA,wA);
    centerform(xB,zB,yB,wB);
    tA=IA[0]->tangentAtEstimate(yA);
    tB=IB[0]->tangentAtEstimate(yB);
  }
  
  /* exit if domain is too large */ {
    double WCUTOFF=0.3;
    if (max(zA[0],zB[0])>6.00) WCUTOFF *=0.3; // things are unstable here!
    if (max(max(wA),max(wB)) >WCUTOFF) return 0;
  }
  
  /* initialize lower and upper corners of A and B */
  double yAn[6],yBn[6],yAu[6],yBu[6];
  lineInterval tAu,tBu,tAn,tBn;
  {
    int k[6]={1,2,3,0,4,5};
    for (int j=0;j<6;j++)
      {
	int u = k[j];
	int sgnA = sgn(tA.Df[u] + (j<3 ? tB.Df[u] : zero ) );
	//if (0==sgnA) return 0;
	yAn[u]= (sgnA>=0 ? xA[u] : zA[u]);
	yAu[u]= (sgnA>=0 ? zA[u] : xA[u]);
	int sgnB = sgn(tB.Df[u] + (j<3 ? tA.Df[u] : zero ) );
	//if (0==sgnB) return 0;
	yBn[u]= (sgnB>=0 ? xB[u] : zB[u]);
	yBu[u]= (sgnB>=0 ? zB[u] : xB[u]);
      }
    tAn=IA[0]->tangentAtEstimate(yAn); tAu=IA[0]->tangentAtEstimate(yAu);
    tBn=IB[0]->tangentAtEstimate(yBn); tBu=IB[0]->tangentAtEstimate(yBu);
    if (!(sameSgnQ(tA,tB,tAn,tBn))) return 0;
    if (!(sameSgnQ(tA,tB,tAu,tBu))) return 0;
    if (interMath::sup(tAu.f + tBu.f) > - fabs(margin))  { return 0; }
  }
  
  // set T , T is the linear adjustment in shared variables at yAu:
  interval e,eps[6];
  e = (tAu.f - tBu.f)/two;
  for (int j=1;j<4;j++) eps[j]= (tAu.Df[j]-tBu.Df[j])/two;
  if ((interMath::sup(tAu.f)> interMath::inf(e)) ||
      (interMath::sup(tAn.f)> interMath::inf(e)) ||
      (interMath::sup(tBu.f)> interMath::inf(-e)) ||
      (interMath::sup(tBn.f)> interMath::inf(-e)) ||
      (interMath::sup(tAn.f+tBn.f)>interMath::sup(tA.f+tB.f)) ||
      (interMath::sup(tA.f+tB.f)>interMath::sup(tAu.f+tBu.f))
      ) return 0;
  interval iyAu1(yAu[1],yAu[1]),iyAu2(yAu[2],yAu[2]),iyAu3(yAu[3],yAu[3]);
  taylorFunction T = taylorSimplex::unit*e +
    (taylorSimplex::x2+taylorSimplex::unit*(-iyAu1))*eps[1] +
    (taylorSimplex::x3+taylorSimplex::unit*(-iyAu2))*eps[2] +
    (taylorSimplex::x4+taylorSimplex::unit*(-iyAu3))*eps[3];
  
  // split:
  taylorFunction A1 = *IA[0]+T*interval("-1");
  taylorFunction B1 = *IB[0]+T;
  const taylorFunction* IA1[1]= {&A1};
  const taylorFunction* IB1[1]= {&B1};
  cellOption option; 
  option.setPrintMode(cellOption::silent);
  if (prove::recursiveVerifier(depth+1,xB,zB,xB,zB,IB1,1,option) && 
      prove::recursiveVerifier(depth+1,xA,zA,xA,zA,IA1,1,option))
    {  return 1; }
  // debug: indicate failed recursiveVerifier.  
  // this should not normally fail this late, if we have done due diligence.
  // cout << "^"; 
  return 0;
}

void statsQ() {
  static const long starting_time = time(0); //  Time out after this many seconds.
  static int statcounter=0;
  static int linefeed=0;
  if (time(0) - starting_time > timeout) {
    error::fatal("time allocation exceeded 50K secs. Bailing out.");
  }
  else if (count(statcounter++,10000)) 
    {
      cout << "[q" << statcounter/10000 << "*10^4]" << flush;
      if (count(linefeed++,10) )
	{
	  cout << " " << flush; 
	  error::printTime();	  
	}
    }
}

/*
  0 return means verification is a total failure (false ineq, fatal error, recursion limits exceeded).
  under normal execution, 0 should never be returned.
  1 means the ineq is true on the domain.
  function should not change any input parameters  except iteration counter in opt.
*/


int prove::recursiveVerifierQ(int depth,
			      const domain& xAd,const domain& xBd,     /// current lower bound
			      const domain& zAd,const domain& zBd,   // current upper bound
			      const taylorFunction* IA[],const taylorFunction* IB[],
			      int Nineq,cellOption& opt)
{
  double xA[6],xB[6],zA[6],zB[6]; 
  int i;
  timeout = opt.timeout;
  for (i=0;i<6;i++)
    {
      xA[i]=xAd.getValue(i); xB[i]=xBd.getValue(i);
      zA[i]=zAd.getValue(i); zB[i]=zBd.getValue(i);
    }
  // symtype 0 none, 1=split, 2=asym,
  if (!fitstogether(xA,xB)) 
    { error::message("Rx-mismatch:"); printit(xA); printit(xB); return 0; }
  if (!fitstogether(zA,zB)) 
    { error::message("Rz-mismatch:"); printit(zA); printit(zB); return 0; }
  statsQ(); 
  opt.augmentIterationCount();
  if ((opt.getIterationLimit()>0)&&
      (opt.getIterationLimit()<opt.getIterationCount()))
    {
      report_failure(xA,zA,"A:iteration limit exceeded");
      report_failure(xB,zB,"B:iteration limit exceeded");
      cout << "iteration limit is set at " << opt.getIterationLimit() << endl;
      return 0 ;
    }
  int MAXDEPTH = 200;
  if (opt.getRecursionDepth()>0) MAXDEPTH=opt.getRecursionDepth();
  if (depth++ > MAXDEPTH) 
    {
      report_failure(xA,zA,"A:recursion limit exceeded");
      report_failure(xB,zB,"B:recursion limit exceeded");
      cout << "recursion depth is currently at " << MAXDEPTH << endl;
      return 0;
    }
  
  /*
    if ((reducible(IA,Nineq) )&&(reducible(IB,Nineq))&&
    (unreducedQ(xA,xB,zA,zB)))
    {
    // should be 0..18
    for (i=opt.getStartingIndex();i<18;i++) 
    if (setreductionQ(i,xA,xB,zA,zB,zzA,zzB))
    {
    if (opt.skip(i)) continue;
    cout << "R" << i << "." << flush;
    if (!recursiveVerifierQ
    (depth,xA,xB,zzA,zzB,IA,IB,Nineq,opt)) { return 0; };
    };
    return 1;
    }
  */
  
  if (opt.dimRedBackSym)
    {
      double xxA[6],xxB[6],zzA[6],zzB[6];
      opt.dimRedBackSym=0;
      for (int i=opt.getStartingIndex();i<8;i++) {
	setDimRedBackSym(i,xA,xB,zA,zB,xxA,xxB,zzA,zzB);
	cout << "R" << i << "." << flush;
	if (!recursiveVerifierQ
	    (depth+1,xxA,xxB,zzA,zzB,IA,IB,Nineq,opt)) { return 0; };
      };
      { return 1; }
    }
  
  
  // make a local copy of data. verifyCellQ etc. change the parameters.
  double xxA[6],xxB[6],zzA[6],zzB[6];
  for (i=0;i<6;i++) 
    {xxA[i]=xA[i];zzA[i]=zA[i];xxB[i]=xB[i];zzB[i]=zB[i];}
  if (Nineq>MAXcount) 
    {
      cout << "There are " << Nineq << " inequalities." << endl;
      error::message("Increase MAXcount and recompile");
      return 0;
    }
  const taylorFunction* IIA[MAXcount];
  const taylorFunction* IIB[MAXcount];
  for (i=0;i<Nineq;i++) { IIA[i]=IA[i];  IIB[i]=IB[i]; }
  int NNineq = Nineq;
  
  
  /*
  // set bound on smaller diagonal:
  // a bad condition was removed on 6/9/97 // if (zzA[3]>8) { etc.
  // stuff that worked with the condition, still works, but this
  // should improve other cases as well.
  double z3=zzA[3];
  if (edgeBound::shortDiagMax(xxA[0],xxB[0],zzA[1],zzA[2],xxA[3],z3,
  zzA[4],zzB[4],zzA[5],zzB[5]))
  {
  if (z3<xxA[3]) return 1;//nothing in domain. We are done.
  if (z3<zzA[3]) { zzA[3]=zzB[3]=z3; } // restrict domain
  }
  */
  
  /* Use top delta to compute upper bound on common diag in quad cluster */ {
    if (opt.crossDiagMinDelta > 0.0) {
      double z = edgeBound::x4_upper_from_top_delta(opt.crossDiagMinDelta,zzA,zzB);
      if (xxA[3] > z) { return 1; } // empty domain.
      if (z < zzA[3]) { zzA[3] = z; zzB[3] = z; }
    }
  }
  
  /* Use "Enclosed" to compute upper bound on common diag in quad cluster. */ {
    if (opt.crossDiagMinEnclosed > 0.0) {
      double z = edgeBound::x4_diag_max(opt.crossDiagMinEnclosed,xxA,xxB,zzA,zzB);
      if (xxA[3] > z) { return 1; } // empty domain.
      if (z < zzA[3]) { zzA[3] = z; zzB[3] = z; }
    }
  }
    
  // Here is the main line of the procedure.  Check if it verifies. 		//xxA,.. affected.
  if (verifyCellQ(xxA,xxB,zzA,zzB,IIA,IIB,NNineq,opt)) return 1;
  
  
  if (NNineq<1) {
    error::message("Empty recursion");
    return 0;
  }
  
  if (breaksapart(depth,xxA,xxB,zzA,zzB,IIA,IIB,NNineq,opt.margin)) return 1;
  
  /* run recursion into two cases.  */ { 
    interMath::up();
    int jB=0, jA=1;
    int j_wide=0; 
    /* init j_wide, jB, jA */ {
      double w = zzA[0]-xxA[0]; 
      for (int j=0;j<DIM6;j++) {
	double w0 = zzA[j]-xxA[j];
	if (w0 > w) { j_wide = j; if ((j>0)&&(j<4)) { jB=1; } else { jB =0; };  w = w0; }
      }
      int k[3]={0,4,5}; // unshared coords.
      for (int j=0;j<3;j++) {
	int j0 = k[j];
	double w0 = zzB[j0]-xxB[j0];
	if (w0 > w) { j_wide = j0; jB = 1; jA=0; w = w0; }
      }}
    for (int k=0;k<2;k++) 	{
      double y, xAr[DIM6], zAr[DIM6], xBr[DIM6], zBr[DIM6];
      y = (jA ? (xxA[j_wide]+zzA[j_wide])/2.0 :  (xxB[j_wide]+zzB[j_wide])/2.0   );
      for (int j=0;j<DIM6;j++) { xAr[j] = xxA[j]; zAr[j]=zzA[j]; }
      for (int j=0;j<DIM6;j++) { xBr[j] = xxB[j]; zBr[j]=zzB[j]; }
      if (jA) { (k? xAr[j_wide] = y : zAr[j_wide] = y); }
      if (jB) { (k? xBr[j_wide] = y : zBr[j_wide] = y); }
      if (!recursiveVerifierQ
	  (depth+1,xAr,xBr,zAr,zBr,IIA,IIB,NNineq,opt)) return 0;
    }
    return 1;
  }}

/*
// now start the old recursion;	
interMath::up();
double yyA[6]; for (i=0;i<6;i++) yyA[i]= (xxA[i]+zzA[i])/2.0;//~center.
double xAr[6],zAr[6];
double yyB[6]; for (i=0;i<6;i++) yyB[i]= (xxB[i]+zzB[i])/2.0;//~center.
for (i=1;i<4;i++) yyB[i]=yyA[i];
double xBr[6],zBr[6];
static const double epsilon_width = 1.0e-8;
for (i=0;i<6;i++) { xAr[i]=xxA[i]; zAr[i]=zzA[i]; }
for (i=0;i<6;i++) { xBr[i]=xxB[i]; zBr[i]=zzB[i]; }
int imaxA[6],imaxB[6],iterA[6],iterB[6];
for (i=0;i<6;i++) { imaxA[i]= ( zzA[i]>xxA[i]+epsilon_width? 2 : 1 ); }
for (i=0;i<6;i++) { imaxB[i]= ( zzB[i]>xxB[i]+epsilon_width? 2 : 1 ); }
double w0=zzA[0]-xxA[0]; 
for (i=1;i<6;i++) 
if (w0<zzA[i]-xxA[i]) w0=zzA[i]-xxA[i]; 
for (i=0;i<6;i++) 
if (w0<zzB[i]-xxB[i]) w0=zzB[i]-xxB[i]; 
w0 = w0/2.0; //  approximate width;
for (i=0;i<6;i++) if ((imaxA[i]>1)&&(zzA[i]-xxA[i]<w0)) imaxA[i]=1;
for (i=0;i<6;i++) if ((imaxB[i]>1)&&(zzB[i]-xxB[i]<w0)) imaxB[i]=1;
for (iterA[0]=0;iterA[0]<imaxA[0];iterA[0]++)  // at most 2^9 cases
for (iterA[1]=0;iterA[1]<imaxA[1];iterA[1]++)
for (iterA[2]=0;iterA[2]<imaxA[2];iterA[2]++)
for (iterA[3]=0;iterA[3]<imaxA[3];iterA[3]++)
for (iterA[4]=0;iterA[4]<imaxA[4];iterA[4]++)
for (iterA[5]=0;iterA[5]<imaxA[5];iterA[5]++)
for (iterB[0]=0;iterB[0]<imaxB[0];iterB[0]++)
for (iterB[4]=0;iterB[4]<imaxB[4];iterB[4]++)
for (iterB[5]=0;iterB[5]<imaxB[5];iterB[5]++)
{
iterB[1]=iterA[1]; iterB[2]=iterA[2]; iterB[3]=iterA[3];
for (i=0;i<6;i++) 
{
xAr[i] = ( iterA[i] ? yyA[i] : xxA[i] );
zAr[i] = ( imaxA[i]-iterA[i]-1? yyA[i] : zzA[i] );
xBr[i] = ( iterB[i] ? yyB[i] : xxB[i] );
zBr[i] = ( imaxB[i]-iterB[i]-1? yyB[i] : zzB[i] );
}
if (!recursiveVerifierQ
(depth+1,xAr,xBr,zAr,zBr,IIA,IIB,NNineq,opt)) return 0;
}
return 1;
}
*/

// end of buffer.
