/* ========================================================================== */
/* FLYSPECK - CODE FORMALIZATION                                              */
/*                                                                            */
/* Chapter: nonlinear inequalities                                                             */
/* Author:  Thomas Hales     */
/* Date: 1997, 2010-09-04                                                    */
/* ========================================================================== */

#include <iomanip>
#include <math.h>
#include <time.h>
#include <stdlib.h>
#include <float.h>
#include "interval.h"
#include "lineInterval.h"
#include "secondDerive.h"
#include "taylorInterval.h"

// parameter passing modes (const-reference parameters)
// http://pages.cs.wisc.edu/~hasti/cs368/CppTutorial/NOTES/PARAMS.html


class primitive
{
private:
	lineInterval (*hfn)(const domain&);

  // all the arrays of double [6][6] are bounds on abs value of second partials.
	int (*setAbsSecond)(const domain& x,const domain& z,double [6][6]);

public:
	lineInterval tangentVectorOf(const domain& x) { return (*hfn)(x); }
	taylorInterval evalf(const domain& w,const domain& x,
		const domain& y,const domain& z) const;
	primitive(lineInterval (*)(const domain& ),
		int (*)(const domain& ,const domain&,double [6][6]));
};

// the various composite functions are held in a linked list.
// f(p1(x),p2(x),...,p6(x)), where x = x1..x6, and f is given by hdr.
// 
class compositeData
{
private:
  const taylorFunction* hdr;
  const taylorFunction* p1;
  const taylorFunction* p2;
  const taylorFunction* p3;
  const taylorFunction* p4;
  const taylorFunction* p5;
  const taylorFunction* p6;
  const compositeData* link;

public:

  compositeData(const taylorFunction* ,
		const taylorFunction*,const taylorFunction*,const taylorFunction*,
		const taylorFunction*,const taylorFunction*,const taylorFunction*,
		const compositeData*);
  compositeData();
  compositeData(const compositeData&);

  compositeData operator+(const compositeData&) const;

  compositeData operator*(const interval&) const;

  taylorInterval evalf(const domain& w,const domain& x,
		const domain& y,const domain& z) const;

  // should add a destructor.
};


class details 
{
public:
    compositeData* cdata;
    primPtr* basisVector;
    interval* basisCoeff;
    int basisCount;
    int basisCapacity;
	details(int capacity) { 
	  cdata=NULL;
		basisCount=basisCapacity=0;
		basisCoeff=0; basisVector=0;
		if (capacity>0) {
			basisCapacity=capacity;
			basisVector= new primPtr[basisCapacity];
			if (!basisVector) error::message("allocation (d1)");
			basisCoeff= new interval[basisCapacity];
			if (!basisCoeff) error::message("allocation (d2)");
			}
		}
	details(const details& rhs)
		{
		  cdata=NULL;
		// cout << "details = " << endl; 
		basisVector = new primPtr[rhs.basisCapacity];
		if (!basisVector) error::message("allocation (d3)");
		basisCoeff = new interval[rhs.basisCapacity];
		if (!basisCoeff) error::message("allocation (d4)");
		basisCount = rhs.basisCount;
		basisCapacity=rhs.basisCapacity;
		for (int i=0;i<basisCapacity;i++)
			{
			basisCoeff[i]=rhs.basisCoeff[i];
			basisVector[i]=rhs.basisVector[i];
			}
		}
	~details() {
		if (basisVector)  delete[] basisVector;
		if (basisCoeff)  delete[] basisCoeff; 
		}
		
};





compositeData::compositeData(const taylorFunction* hdr0, 
  const taylorFunction* p10,const taylorFunction* p20,const taylorFunction* p30,
  const taylorFunction* p40,const taylorFunction* p50,const taylorFunction* p60, 
			     const compositeData* c) {
  hdr = hdr0;
  p1 = p10;
  p2 = p20;
  p3 = p30;
  p4 = p40;
  p5 = p50;
  p6 = p60;
  link = c;
};


compositeData::compositeData() {
  hdr = NULL;
  p1 = NULL;
  p2 = NULL;
  p3 = NULL;
  p4 = NULL;
  p5 = NULL;
  p6 = NULL;
  link = NULL;
};

// copy.
compositeData::compositeData(const compositeData& c) {
  hdr = c.hdr;
  p1 = c.p1;
  p2 = c.p2;
  p3 = c.p3;
  p4 = c.p4;
  p5 = c.p5;
  p6 = c.p6;
  link = c.link;
};


compositeData compositeData::operator+(const compositeData& b) const {
  compositeData a(*this);
  if (!link) {
    a.link = &b;
    return a;
  }
  compositeData c(*link);
  a.link = 0;
  return a + (c + b);
};


compositeData compositeData::operator*(const interval& t)  const {
  compositeData a(*this);
  if (hdr) { 
    a.hdr = (new taylorFunction((*hdr) * t)); 
  }
  if (link) { 
    a.link = (new compositeData((*link) * t)); 
  }
  return a;
};


static inline double dabs(const interval x)
    {
    return interMath::sup(interMath::max(x,-x));
    }


taylorInterval compositeData::evalf(const domain& w,const domain& x,const domain& y,const domain& z ) const
{
  if (!hdr) { error::fatal ("evalf: function expected, returning 0");   }

  taylorInterval pv[6];
  pv[0] = p1->evalf4(w,x,y,z);
  pv[1] = p2->evalf4(w,x,y,z);
  pv[2] = p3->evalf4(w,x,y,z);
  pv[3] = p4->evalf4(w,x,y,z);
  pv[4] = p5->evalf4(w,x,y,z);
  pv[5] = p6->evalf4(w,x,y,z);
  // calculate wide value range of pv[i], 
  double a[6], b[6];
  for (int i =0;i<6;i++) {
    a[i] = pv[i].lowerBound(); b[i] = pv[i].upperBound(); 
    //cout << "aW,bW" << a[i] << " " << b[i] << endl; // DEBUG.
  }
  domain aW(a);
  domain bW(b);
  // calculate narrow value range of pv[i].
  for (int i=0;i<6;i++) {
    a[i]=pv[i].tangentVectorOf().low(); b[i] =pv[i].tangentVectorOf().hi();
    //cout << "aN,bN " << a[i] << " " << b[i] << endl; // DEBUG.
  }
  domain aN(a);
  domain bN(b);

  // value of outer function
  taylorInterval fW = hdr->evalf(aW,bW);
  taylorInterval fN = hdr->evalf(aN,bN);
  // derivatives of outer function
  interval fW_partial[6]; // wide partials (over entire domain)
  interval fN_partial[6]; // narrow partials (at interval image of a point)
  interval pW_partial[6][6]; // function i, partial j.
  interval pN_partial[6][6];  
  for (int i=0;i<6;i++) {
    interval tW(fW.lowerPartial(i),fW.upperPartial(i));
    fW_partial[i] = tW;
    interval tN(fN.lowerPartial(i),fN.upperPartial(i));
    fN_partial[i] = tN;
    //cout << "f" << i << " " << fN_partial[i] << " " << fW_partial[i] << endl; // DEBUG.
    for (int j=0;j<6;j++) {
      interval uW(pv[i].lowerPartial(j),pv[i].upperPartial(j));
      pW_partial[i][j] = uW;
      pN_partial[i][j] = pv[i].tangentVectorOf().partial(j);
      // cout << "p i j " << i << j << " " << pW_partial[i][j] << " " << pN_partial[i][j] << endl; // DEBUG
    }
  }
  // apply chain rule to compute narrow first derivative data.
  interval cN_partial[6];
  static interval zero("0");
  for (int i=0;i<6;i++) {
    cN_partial[i] = zero;
    for (int j=0;j<6;j++) { cN_partial[i]  =cN_partial[i] + fN_partial[j] * pN_partial[j][i]; }
  }
  // apply chain rule to compute bound on second derivative data. 
  // This is the "wide" part of the calc.
  double DcW[6][6];
  interMath::up();
  for (int i=0;i<6;i++) for (int j=0;j<6;j++) {
      DcW[i][j]= 0.0;
      for (int k=0;k<6;k++) {
	DcW[i][j] = DcW[i][j] + dabs(fW_partial[k]) * pv[k].DD[i][j];
	for (int m=0;m<6;m++) {
	  DcW[i][j] = DcW[i][j] + fW.DD[k][m] * dabs(pW_partial[k][i]) * dabs(pW_partial[m][j]);
	}
      }
    }
  lineInterval lin;
  lin.f = fN.tangentVectorOf().f;
  for (int i=0;i<6;i++) {
    lin.Df[i] = cN_partial[i];
  }
  taylorInterval ch(1,lin,w,DcW);
  // if there is a link add it recursively.
  if (!link) {
    return ch;
  }
  else {
    return taylorInterval::plus(ch , link->evalf(w,x,y,z));
  }
};


taylorInterval primitive::evalf
	(const domain& w,const domain& x,const domain& y,const domain& z) const
	{
	double DD[6][6];
	int s = (*setAbsSecond)(x,z,DD);
	lineInterval tangentVector = (*hfn)(y);
	return taylorInterval(s,tangentVector,w,DD);
	}

static inline double max(double x,double y)
	{ return (x>y ? x : y); }

taylorInterval taylorFunction::evalf4
(const domain& w, const domain& x,const domain& y, const domain& z) const
    {	
    if (X->basisCount<1) { error::message("empty function encountered"); }
    taylorInterval t = taylorInterval::scale(
        X->basisVector[0]->evalf(w,x,y,z),X->basisCoeff[0]);
    for (int i=1;i<X->basisCount;i++)
        t = taylorInterval::plus(t,
                taylorInterval::scale((X->basisVector[i]->evalf(w,x,y,z)),
                                        (X->basisCoeff[i])));
    return t;
    }

taylorInterval taylorFunction::evalf
    (const domain& x,const domain& z) const
    {
	double w[6],y[6];
	int i;
	interMath::nearest();
	for (i=0;i<6;i++) y[i]=(z.getValue(i)+x.getValue(i))/2.0;
	interMath::up();
	for (i=0;i<6;i++) w[i]=max(z.getValue(i)-y[i],
						y[i]-x.getValue(i));
	domain wD(w[0],w[1],w[2],w[3],w[4],w[5]);
	domain yD(y[0],y[1],y[2],y[3],y[4],y[5]);
	
	//return taylorFunction::evalf4(wD,x,yD,z);
	
    if (X->basisCount<1) { error::message("empty function encountered"); }
    taylorInterval t = taylorInterval::scale(
        X->basisVector[0]->evalf(wD,x,yD,z),X->basisCoeff[0]);
    for (i=1;i<X->basisCount;i++)
        t = taylorInterval::plus(t,
                taylorInterval::scale((X->basisVector[i]->evalf(wD,x,yD,z)),
                                        (X->basisCoeff[i])));
    return t;
       
    }

void taylorFunction::setReducibleState(int i)
	{ reduState = i; }
int taylorFunction::getReducibleState() const
	{ return reduState; }

lineInterval taylorFunction::evalAt(const domain& x) const
	{
	lineInterval total;
	lineInterval temp;
	interval c;
	int i,j;
	if (X->basisCount<1) { error::message("empty function encountered"); }
    for (i=0;i<X->basisCount;i++)
		{
        temp = X->basisVector[i]->tangentVectorOf(x);
		c = X->basisCoeff[i];
		total.f = total.f + c*temp.f;
		for (j=0;j<6;j++)
		total.Df[j]= total.Df[j]+ c*temp.Df[j];
		}
    return total;
	}

primitive::primitive(lineInterval (*hfn0)(const domain&),
	int (*setAbsSecond0)(const domain&,const domain&,double [6][6]))
	{
	hfn = hfn0;
	setAbsSecond = setAbsSecond0;
	}


taylorInterval::taylorInterval(int s,const lineInterval& h0,
	const domain& w0,const double DD0[6][6])
	{
	w = w0;
	int i,j;
	validDataFlag = s;
	tangentVector = h0;
	if (s) for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=DD0[i][j];
	}

int taylorInterval::isValidData() const
	{ return validDataFlag; }

lineInterval taylorInterval::tangentVectorOf() const
	{
	static const interval zero("0");
	if (!validDataFlag) 
		{ error::message("center computation failed"); 
		  return lineInterval(zero); }
	return tangentVector;
	}

static double taylorError(const domain& w,const double sec[6][6])
    {
    interMath::up();
    double t=0.0;
    int i,j;
    for (i=0;i<6;i++) for (j=0;j<6;j++) {
	if (sec[i][j] < 0.0) { error::message("negative abs in taylorError"); }
      }
    for (i=0;i<6;i++) t = t + (w.getValue(i)*w.getValue(i))*sec[i][i];
    t = t/2.0;
    for (i=0;i<6;i++) for (j=i+1;j<6;j++)
        t = t+ (w.getValue(i)*w.getValue(j))*sec[i][j];
    return t;
    }



double taylorInterval::upperBound() const
	{
	if (!validDataFlag) 
		{
		error::message("upperBound computation failed");
		return 0;
		}
	double err = taylorError(w,DD);
	interMath::up();
    double t = tangentVector.hi() + err;
    for (int i=0;i<6;i++) t = t+ w.getValue(i)*dabs(tangentVector.partial(i));
    return t;
    }

double taylorInterval::lowerBound() const
	{
	if (!validDataFlag) 
		{
		error::message("lowerBound computation failed");
		return 0;
		}
	double err = taylorError(w,DD);
	interMath::down();
    double t = tangentVector.low() - err;
    for (int i=0;i<6;i++) t = t + (-w.getValue(i))*dabs(tangentVector.partial(i));
    return t;
    }

double taylorInterval::upperboundQ
	(const taylorInterval& cA,const taylorInterval& cB)
    {
	if ((!cA.validDataFlag)||(!cB.validDataFlag))
		{
		error::message("upperBoundQ failed");
		return 0;
		}
    interMath::up();
	double err = taylorError(cA.w,cA.DD)+taylorError(cB.w,cB.DD);
    double t = cA.tangentVector.hi()+cB.tangentVector.hi() + err;
    int k[3]={0,4,5},i;
    for (i=0;i<3;i++) t = 
		t+ cA.w.getValue(k[i])*dabs(cA.tangentVectorOf().partial(k[i]));
    for (i=0;i<3;i++) t = 
		t+ cB.w.getValue(k[i])*dabs(cB.tangentVectorOf().partial(k[i]));
    for (i=1;i<4;i++) t = t+ cB.w.getValue(i)*
		dabs(cB.tangentVectorOf().partial(i)+cA.tangentVectorOf().partial(i));
    return t;
    }
 
double taylorInterval::lowerboundQ
	(const taylorInterval& cA,const taylorInterval& cB)
    {
	if ((!cA.validDataFlag)||(!cB.validDataFlag))
		{
		error::message("upperBoundQ failed");
		return 0;
		}
    interMath::up();
	double err = taylorError(cA.w,cA.DD)+taylorError(cB.w,cB.DD);
	interMath::down();
    double t = cA.tangentVector.low()+cB.tangentVector.low() - err;
    int k[3]={0,4,5},i;
    for (i=0;i<3;i++) t = t+ 
		(-cA.w.getValue(k[i]))*dabs(cA.tangentVectorOf().partial(k[i]));
    for (i=0;i<3;i++) t = t+ 
		(-cB.w.getValue(k[i]))*dabs(cB.tangentVectorOf().partial(k[i]));
    for (i=1;i<4;i++) t = t+ (-cB.w.getValue(i))
		*dabs(cB.tangentVectorOf().partial(i)+cA.tangentVectorOf().partial(i));
    return t;
    }


double taylorInterval::upperPartial(int i) const
	{
	if ((i<0)||(i>=6)) 
		{ error::message("upperPartial index out of range"); return 0; }
	if (!validDataFlag) 
		{
		error::message("upperPartial computation failed");
		return 0;
		}
	interMath::up();
	double err = 0.0;
	for (int j=0;j<6;j++) err  = err + w.getValue(j)*DD[i][j];
	return interMath::sup(tangentVector.partial(i)) + err;
	}

double taylorInterval::lowerPartial(int i) const
	{
	if ((i<0)||(i>=6)) 
		{ error::message("upperPartial index out of range"); return 0; }
	if (!validDataFlag) 
		{
		error::message("lowerParial computation failed");
		return 0;
		}
	interMath::up();
	double err = 0.0;
	for (int j=0;j<6;j++) err  = err + w.getValue(j)*DD[i][j];
	interMath::down();
	return interMath::inf(tangentVector.partial(i)) - err;
	}

/*
static double doi(const interval x) {
  return interMath::sup(interMath::max(x,-x));
}
*/

static void intervalToDouble(const interval DDx[6][6],double DD[6][6])
	{
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) 	DD[i][j]= dabs(DDx[i][j]);
	}

/******************************* taylorSimplex functions ****************/

/*implement unit*/
static int setZero(const domain& ,const domain& ,double DD[6][6])
	{
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
	return 1;
	}
static lineInterval unit(const domain& )
	{
	static const interval one("1");
	return lineInterval(one);
	}
primitive scalr(unit,setZero);
const taylorFunction taylorSimplex::unit(scalr);

/*implement x1 */
static lineInterval lineX1(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(0),x.getValue(0)));
	h.Df[0]=one;
	return h;
	}
primitive x1(lineX1,setZero);
const taylorFunction taylorSimplex::x1(::x1);
/*implement x2 */
static lineInterval lineX2(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(1),x.getValue(1)));
	h.Df[1]=one;
	return h;
	}
primitive x2(lineX2,setZero);
const taylorFunction taylorSimplex::x2(::x2);

/*implement x3 */
static lineInterval lineX3(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(2),x.getValue(2)));
	h.Df[2]=one;
	return h;
	}
primitive x3(lineX3,setZero);
const taylorFunction taylorSimplex::x3(::x3);

/*implement x4 */
static lineInterval lineX4(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(3),x.getValue(3)));
	h.Df[3]=one;
	return h;
	}
primitive x4(lineX4,setZero);
const taylorFunction taylorSimplex::x4(::x4);

/*implement x5 */
static lineInterval lineX5(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(4),x.getValue(4)));
	h.Df[4]=one;
	return h;
	}
primitive x5(lineX5,setZero);
const taylorFunction taylorSimplex::x5(::x5);

/*implement x6 */
static lineInterval lineX6(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(5),x.getValue(5)));
	h.Df[5]=one;
	return h;
	}
primitive x6(lineX6,setZero);
const taylorFunction taylorSimplex::x6(::x6);

/*implement y1 */
static lineInterval sqrt(lineInterval a)
    {
    lineInterval temp;
	static const interval one("1");
	static const interval two("2");
    temp.f = interMath::sqrt(a.f);
    interval rs = one/(two*temp.f);
    int i;
    for (i=0;i<6;i++) temp.Df[i]=rs*a.Df[i];
    return temp;
    }

static lineInterval lineY1(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(0),x.getValue(0)));
	h.Df[0]=one;
	return sqrt(h);
	}

static int setY1(const domain& x,const domain&,double DD[6][6])
	{
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
	double x0 = x.getValue(0);
	if (x0<1.0e-8) return 0;
	interMath::down();
	double y = sqrt(x0);
	double y3 = 4.0*y*y*y;
	interMath::up();
	if (y3</*float.h*/DBL_EPSILON) return 0;
	DD[0][0]= 1.0/y3;
	return 1;
	}
primitive Y1(lineY1,setY1);
const taylorFunction taylorSimplex::y1(::Y1);

/*implement y2 */
static lineInterval lineY2(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(1),x.getValue(1)));
	h.Df[1]=one;
	return sqrt(h);
	}
static int setY2(const domain& x,const domain&,double DD[6][6])
	{
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
	double x0 = x.getValue(1);
	if (x0<1.0e-8) return 0;
	interMath::down();
	double y = sqrt(x0);
	double y3 = 4.0*y*y*y;
	if (y3</*float.h*/DBL_EPSILON) return 0;
	interMath::up();
	DD[1][1]= 1.0/y3;
	return 1;
	}
primitive Y2(lineY2,setY2);
const taylorFunction taylorSimplex::y2(::Y2);

/*implement y3 */
static lineInterval lineY3(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(2),x.getValue(2)));
	h.Df[2]=one;
	return sqrt(h);
	}
static int setY3(const domain& x,const domain&,double DD[6][6])
	{
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
	double x0 = x.getValue(2);
	if (x0<1.0e-8) return 0;
	interMath::down();
	double y = sqrt(x0);
	double y3 = 4.0*y*y*y;
	if (y3</*float.h*/DBL_EPSILON) return 0;
	interMath::up();
	DD[2][2]= 1.0/y3;
	return 1;
	}
primitive Y3(lineY3,setY3);
const taylorFunction taylorSimplex::y3(::Y3);

/*implement y4 */
static lineInterval lineY4(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(3),x.getValue(3)));
	h.Df[3]=one;
	return sqrt(h);
	}
static int setY4(const domain& x,const domain&,double DD[6][6])
	{
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
	double x0 = x.getValue(3);
	if (x0<1.0e-8) return 0;
	interMath::down();
	double y = sqrt(x0);
	double y3 = 4.0*y*y*y;
	if (y3</*float.h*/DBL_EPSILON) return 0;
	interMath::up();
	DD[3][3]= 1.0/y3;
	return 1;
	}
primitive Y4(lineY4,setY4);
const taylorFunction taylorSimplex::y4(::Y4);

/*implement y5 */
static lineInterval lineY5(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(4),x.getValue(4)));
	h.Df[4]=one;
	return sqrt(h);
	}
static int setY5(const domain& x,const domain&,double DD[6][6])
	{
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
	double x0 = x.getValue(4);
	if (x0<1.0e-8) return 0;
	interMath::down();
	double y = sqrt(x0);
	double y3 = 4.0*y*y*y;
	if (y3</*float.h*/DBL_EPSILON) return 0;
	interMath::up();
	DD[4][4]= 1.0/y3;
	return 1;
	}
primitive Y5(lineY5,setY5);
const taylorFunction taylorSimplex::y5(::Y5);

/*implement y6 */
static lineInterval lineY6(const domain& x)
	{
	static const interval one("1");
	lineInterval h(interval(x.getValue(5),x.getValue(5)));
	h.Df[5]=one;
	return sqrt(h);
	}
static int setY6(const domain& x,const domain&,double DD[6][6])
	{
	for (int i=0;i<6;i++) for (int j=0;j<6;j++) DD[i][j]=0.0;
	double x0 = x.getValue(5);
	if (x0<1.0e-8) return 0;
	interMath::down();
	double y = sqrt(x0);
	double y3 = 4.0*y*y*y;
	if (y3</*float.h*/DBL_EPSILON) return 0;
	interMath::up();
	DD[5][5]= 1.0/y3;
	return 1;
	}
primitive Y6(lineY6,setY6);
const taylorFunction taylorSimplex::y6(::Y6);


/*implement delta */
static int setAbsDelta(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
	interval DDh[6][6];
	int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	secondDerive::setDelta(X,Z,DDh);
	intervalToDouble(DDh,DD);
	return 1;
	}
primitive deltaPrimitive(linearization::delta,setAbsDelta);
const taylorFunction taylorSimplex::delta(::deltaPrimitive);

/*implement dih1*/
static int setDihedral(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
	int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	return secondDerive::setAbsDihedral(X,Z,DD);
	}
primitive dih1Primitive(linearization::dih,setDihedral);
const taylorFunction taylorSimplex::dih(::dih1Primitive);

/*implement dih2*/
static int setDih2(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
	int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	interval s,Ds[6],DDs[6][6];
	int outcome = secondDerive::setSqrtDelta(X,Z,s,Ds,DDs);
	if (!outcome) return outcome;
	interval h,Dh[6],DDh[6][6];
	outcome = secondDerive::setDih2(X,Z,s,Ds,DDs,h,Dh,DDh);
	if (!outcome) return outcome;
	intervalToDouble(DDh,DD);
	return outcome;
	}
primitive dih2Primitive(linearization::dih2,setDih2);
const taylorFunction taylorSimplex::dih2(::dih2Primitive);

/*implement dih3*/
static int setDih3(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
	int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	interval s,Ds[6],DDs[6][6];
	int outcome = secondDerive::setSqrtDelta(X,Z,s,Ds,DDs);
	if (!outcome) return outcome;
	interval h,Dh[6],DDh[6][6];
	outcome = secondDerive::setDih3(X,Z,s,Ds,DDs,h,Dh,DDh);
	if (!outcome) return outcome;
	intervalToDouble(DDh,DD);
	return outcome;
	}
primitive dih3Primitive(linearization::dih3,setDih3);
const taylorFunction taylorSimplex::dih3(::dih3Primitive);

/*implement azim*/
static int setRhazim(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
	int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	interval s,Ds[6],DDs[6][6];
	int outcome = secondDerive::setSqrtDelta(X,Z,s,Ds,DDs);
	if (!outcome) return outcome;
	interval h,Dh[6],DDh[6][6];
	outcome = secondDerive::setDihedral(X,Z,s,Ds,DDs,h,Dh,DDh);
	if (!outcome) return outcome;
	interval DDa[6][6];
	outcome = secondDerive::setRhazim(X[0],Z[0],h,Dh,DDh,DDa);
	intervalToDouble(DDa,DD);
	return outcome;
	}
primitive rhazimPrimitive(linearization::rhazim,setRhazim);
const taylorFunction taylorSimplex::rhazim(::rhazimPrimitive);

/*implement azim2*/
static int setRhazim2(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
	int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	interval s,Ds[6],DDs[6][6];
	int outcome = secondDerive::setSqrtDelta(X,Z,s,Ds,DDs);
	if (!outcome) return outcome;
	interval h,Dh[6],DDh[6][6];
	outcome = secondDerive::setDih2(X,Z,s,Ds,DDs,h,Dh,DDh);
	if (!outcome) return outcome;
	interval DDa[6][6];
	outcome = secondDerive::setRhazim2(X[1],Z[1],h,Dh,DDh,DDa);
	intervalToDouble(DDa,DD);
	return outcome;
	}
primitive rhazim2Primitive(linearization::rhazim2,setRhazim2);
const taylorFunction taylorSimplex::rhazim2(::rhazim2Primitive);

/*implement azim3*/
static int setRhazim3(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
	int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	interval s,Ds[6],DDs[6][6];
	int outcome = secondDerive::setSqrtDelta(X,Z,s,Ds,DDs);
	if (!outcome) return outcome;
	interval h,Dh[6],DDh[6][6];
	outcome = secondDerive::setDih3(X,Z,s,Ds,DDs,h,Dh,DDh);
	if (!outcome) return outcome;
	interval DDa[6][6];
	outcome = secondDerive::setRhazim3(X[2],Z[2],h,Dh,DDh,DDa);
	intervalToDouble(DDa,DD);
	return outcome;
	}
primitive rhazim3Primitive(linearization::rhazim3,setRhazim3);
const taylorFunction taylorSimplex::rhazim3(::rhazim3Primitive);


/*implement sol*/
static int setSol(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
    int i,j;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
    interval s,Ds[6],DDs[6][6],DDx[6][6];
    if (!(secondDerive::setSqrtDelta(X,Z,s,Ds,DDs))) return 0;
    if (!(secondDerive::setSolid(X,Z,s,Ds,DDs,DDx))) return 0;
    for (i=0;i<6;i++) for (j=i;j<6;j++)
        DD[i][j]=dabs(DDx[i][j]);
    for (i=0;i<6;i++) for (j=0;j<i;j++) DD[i][j]=DD[j][i];
    return 1;
    }
primitive solPrimitive(linearization::solid,setSol);
const taylorFunction taylorSimplex::sol(::solPrimitive);


static int copy(double DD[6][6],const double sec[6][6])
    {
    for (int i=0;i<6;i++) for (int j=0;j<6;j++)
        DD[i][j]=sec[i][j];
    return 1;
    }


/*implement eta2_126*/
static int setEta2_126(const domain& x,const domain& z,double DD[6][6])
	{
	// use bounds from SECOUT/out.eta2
	static const int k[3]={0,1,5};
	x.getValue(0); // useless line
	z.getValue(0); // useless line
	int i,j;
	for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=0.0;
	for (i=0;i<3;i++) for (j=0;j<3;j++) DD[k[i]][k[j]]=0.09;
	return 1;
	}
primitive eta2Primitive(linearization::eta2,setEta2_126);
const taylorFunction taylorSimplex::eta2_126(::eta2Primitive);

/*implement eta2_135*/
static int setEta2_135(const domain& x,const domain& z,double DD[6][6])
    {
    // use bounds from SECOUT/out.eta2
    static const int k[3]={0,2,4};
	x.getValue(0); // useless line
	z.getValue(0); // useless line
    int i,j;
    for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=0.0;
    for (i=0;i<3;i++) for (j=0;j<3;j++) DD[k[i]][k[j]]=0.09;
	return 1;
    }
primitive eta2_135_Primitive(linearization::eta2_135,setEta2_135);
const taylorFunction taylorSimplex::eta2_135(::eta2_135_Primitive);

/*implement eta2_234*/
static int setEta2_234(const domain& x,const domain& z,double DD[6][6])
    {
    // use bounds from SECOUT/out.eta2
    static const int k[3]={1,2,3};
	x.getValue(0); // useless line
	z.getValue(0); // useless line
    int i,j;
    for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=0.0;
    for (i=0;i<3;i++) for (j=0;j<3;j++) DD[k[i]][k[j]]=0.09;
	return 1;
    }
primitive eta2_234_Primitive(linearization::eta2_234,setEta2_234);
const taylorFunction taylorSimplex::eta2_234(::eta2_234_Primitive);

/*implement eta2_456*/
static int setEta2_456(const domain& x,const domain& z,double DD[6][6])
    {
    // use bounds from SECOUT/out.eta2
    static const int k[3]={3,4,5};
	x.getValue(0); // useless line
	z.getValue(0); // useless line
    int i,j;
    for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=0.0;
    for (i=0;i<3;i++) for (j=0;j<3;j++) DD[k[i]][k[j]]=0.09;
	return 1;
    }
primitive Peta2_456(linearization::eta2_456,setEta2_456);
const taylorFunction taylorSimplex::eta2_456(::Peta2_456);

static int primHasDeltaDenom(const primitive* p) {
  return
    ((p == &dih1Primitive) || (p == &dih2Primitive) || (p == &dih3Primitive) ||
    (p == &rhazimPrimitive) || (p== &rhazim2Primitive) || (p == &rhazim3Primitive) ||
     (p == &solPrimitive));
}


/******************** MORE GENERAL STUFF **************************/

int taylorFunction::hasDeltaDenom() const {
	taylorFunction u  (*this);
	for (int i=0;i<u.X->basisCount;i++) 
		{
		  if (primHasDeltaDenom((u.X->basisVector[i]))) { return 1; }
		}
	return 0;
}

taylorFunction::taylorFunction(int c) { X = new details(c); 
		reduState=0;
		if (!X) error::message("allocation (X)");
		if (X->basisCapacity != c) error::message("capacity not initialized"); }

taylorFunction::taylorFunction(primitive& x)
	{
	reduState=0;
	static const interval one("1");
	X = new details(1);
	if (!X) error::message("allocation (X1)");
	X->basisVector[0]= &x;
	X->basisCoeff[0]= one;
	X->basisCount=1;
	X->basisCapacity=1;
	}

taylorFunction::taylorFunction(const taylorFunction& f)
	{
	X = new details(f.X->basisCapacity);
	if (!X) error::message("allocation (X2)");
	int i;
	for (i=0;i<f.X->basisCount;i++) 
		{
		X->basisVector[i]= f.X->basisVector[i];
		X->basisCoeff[i] = f.X->basisCoeff[i];
		}
	X->basisCount = f.X->basisCount;
	reduState=f.reduState;
	}

taylorFunction& taylorFunction::operator=(const taylorFunction& ) 
	{
	error::message("assignment not implemented");
	return *this;
	}

taylorFunction::~taylorFunction()
	{
	if (X) delete X;
	}

taylorFunction taylorFunction::operator*(const interval& t) const
	{
	taylorFunction u  (*this);
	for (int i=0;i<u.X->basisCount;i++) 
		{
		u.X->basisCoeff[i]= t*u.X->basisCoeff[i];
		u.X->basisVector[i] = u.X->basisVector[i];
		}
	return u;
	}

taylorFunction taylorFunction::operator+(const taylorFunction& f) const
	{
	static const interval zero("0");
	static const int increment = 10;
	taylorFunction a(*this);
    int i,j,match;
    for (i=0;i<f.X->basisCount;i++)
        {
		if (f.X->basisCoeff[i]==zero) continue; // added 12/14/97
        match=0;
        for (j=0;j<a.X->basisCount;j++)
            {
            if (match) continue;
            if (a.X->basisVector[j]==f.X->basisVector[i])
                {
                a.X->basisCoeff[j]=a.X->basisCoeff[j]+f.X->basisCoeff[i];
                match=1;
                }
            }
        if (!match)
            {
            if (a.X->basisCount>=a.X->basisCapacity) 
				{
				int cap = a.X->basisCapacity;
				if (a.X->basisCount>cap) error::message("overflow");
				int r;
				primPtr *temp = new primPtr [cap+increment];
				//cout <<"(1)" << flush;
				if (!temp) error::message("allocation (temp)");
				interval* stemp = new interval[cap+increment];
				//cout <<"(2)"<<flush;
				if (!stemp) error::message("allocation (stemp)");
				for (r =0;r<cap;r++)
					{
					temp[r]= a.X->basisVector[r];
					stemp[r]= a.X->basisCoeff[r];
					}
				delete[] a.X->basisVector;
				delete[] a.X->basisCoeff;

				//VER1.
				/*
				a.X->basisVector = temp;
				a.X->basisCoeff= stemp;
				a.X->basisCapacity = cap+increment;
				*/

				a.X->basisVector = new primPtr[cap+increment];
				//cout <<"(3)"<<flush;
				if (!a.X->basisVector) 
					error::message("allocation (a.X->bV)");
				a.X->basisCoeff= new interval[cap+increment];
				//cout <<"(4)"<<flush;
				if (!a.X->basisCoeff) error::message("allocation (a.X->bC)");
				a.X->basisCapacity = cap+ increment;
				for (r =0;r<cap;r++)
					{
					a.X->basisVector[r]=temp[r];
					a.X->basisCoeff[r]=stemp[r];
					}
				delete[] temp;
				delete[] stemp;
				}
            a.X->basisVector[a.X->basisCount]=f.X->basisVector[i];
            a.X->basisCoeff[a.X->basisCount]=f.X->basisCoeff[i];
            a.X->basisCount++;
            }
        }
	return a;
    }

taylorInterval taylorInterval::plus
	(const taylorInterval& t1,const taylorInterval& t2)
	{
	int flag = t1.isValidData() && t2.isValidData();
	double DD[6][6];
	int i,j;
	interMath::up();
	for (i=0;i<6;i++) for (j=0;j<6;j++) 
		DD[i][j]= t1.DD[i][j]+t2.DD[i][j];
	lineInterval s;
	s.f = t1.tangentVector.f + t2.tangentVector.f;
	for (i=0;i<6;i++) s.Df[i]= t1.tangentVector.Df[i]+ t2.tangentVector.Df[i];
	for (i=0;i<6;i++) if (t1.w.getValue(i)!=t2.w.getValue(i)) 
		error::message("bad domain in ti");
	taylorInterval t(flag,s,t1.w,DD);
	return t;
	}

taylorInterval taylorInterval::scale
	(const taylorInterval& t1,const interval& c)
	{
	int flag = t1.isValidData();
	double absC = interMath::sup(interMath::max(c,-c));
	double DD[6][6];
	int i,j;
	interMath::up();
	for (i=0;i<6;i++) for (j=0;j<6;j++) 
		DD[i][j]= t1.DD[i][j]*absC;
	lineInterval s = t1.tangentVector;
	s.f = s.f*c;
	for (i=0;i<6;i++) s.Df[i]=s.Df[i]*c;
	taylorInterval t(flag,s,t1.w,DD);
	return t;
	}

/************************* TESTING ROUTINES **************************/

static int epsilonClose(double x,interval y,double epsilon)
    {
    if (interMath::abs(y-interval(x,x))>epsilon)
        {
        cout << "close : " << interMath::abs(y-interval(x,x))
              << " " << x << " " << y << endl<< flush;
        return 0;
        }
    return 1;
    }

static int barelyLess(double x,double y,double epsilon)
	{
	if ((x>y)||(y>x+epsilon))
		{
		cout << "barelyLess " << x << " " << y << endl << flush;
		return 0;
		}
	return 1;
	}

static double rand01()
    {
    static int w =0;
    if (w==0) { srand(time(0)); w = 1; }
    double u = double(rand());
    double v = double(/*stdlib.h*/RAND_MAX);
    return u/v;
    }

static double rand(int i,const domain& x,const domain& z,double t=1)
	{
	return x.getValue(i) + t*rand01()*(z.getValue(i)-x.getValue(i));
	}

static domain makeDomain(int i,const domain& x,const domain& z)
	{
	int a[6]; int b=1;
	int j;
	for (j=0;j<6;j++)
		{
		a[j]= (i/b) % 2; // binary conversion
		b= b*2;
		}
	return domain(
		x.getValue(0)+ a[0]*(z.getValue(0)-x.getValue(0)),
		x.getValue(1)+ a[1]*(z.getValue(1)-x.getValue(1)),
		x.getValue(2)+ a[2]*(z.getValue(2)-x.getValue(2)),
		x.getValue(3)+ a[3]*(z.getValue(3)-x.getValue(3)),
		x.getValue(4)+ a[4]*(z.getValue(4)-x.getValue(4)),
		x.getValue(5)+ a[5]*(z.getValue(5)-x.getValue(5)));
	}

//////////
//
// This compares the corners with the taylor upper bound.
// If the taylor upper bound is not close to the corner upper bound
// or if the taylor upper bound is less than a corner value, and
// error is issued.  There can be false reporting of errors here
// because the computed corner value might be much larger than
// the actual corner value (because of atan approximations, etc. ).
// Or the taylor upper bound might be extremely conservative and
// give an upper bound that is much bigger than needs be.

static void testProcedure(taylorFunction F,lineInterval (*G)(const domain&),
	const domain& x,const domain& z,char* s,double epsilon=1.0e-9)
	{
	double t = 1.0e-5; 
	domain xx(rand(0,x,z),rand(1,x,z),rand(2,x,z),
				rand(3,x,z),rand(4,x,z),rand(5,x,z));
	domain zz(rand(0,xx,z,t),rand(1,xx,z,t),rand(2,xx,z,t),
				rand(3,xx,z,t),rand(4,xx,z,t),rand(5,xx,z,t));
	taylorInterval f = F.evalf(xx,zz); // evaluate f at random small cell.

	/*get max*/{
	int i,j;
	double temp = -/*float.h*/DBL_MAX; 
	double Dtemp[6]; for (i=0;i<6;i++) Dtemp[i]= -DBL_MAX;
	for (i=0;i<64;i++) 
		{
		domain c = makeDomain(i,xx,zz); 
		lineInterval li = (*G)(c);
		if (temp<li.hi()) temp = li.hi();
		for (j=0;j<6;j++) if (Dtemp[j]<interMath::sup(li.partial(j)))
			Dtemp[j]=interMath::sup(li.partial(j));
		}
	for (int k=0;k<6;k++) 
	if (!barelyLess(Dtemp[k],f.upperPartial(k),epsilon))
		{
		cout << "testProc Dmax("<<k<<") failed " << s << endl;
		cout << "found = " << Dtemp[k] << " bounded by = " << 
			f.upperPartial(k) << endl;
		interMath::up();
		cout << "diff = " << f.upperPartial(k) - Dtemp[k] << endl;
		for (j=0;j<6;j++) cout << xx.getValue(j) << " "; cout << endl;
		for (j=0;j<6;j++) cout << zz.getValue(j) << " "; cout << endl;
		}
	if (!barelyLess(temp,f.upperBound(),epsilon))
		{
		cout << "\n\ntestProc max failed " << s << endl;
		cout << "found = " << temp << " bounded by = " << f.upperBound() << endl;
		cout << "diff = " << f.upperBound() - temp << endl;
		for (j=0;j<6;j++) cout << xx.getValue(j) << " "; cout << endl;
		for (j=0;j<6;j++) cout << zz.getValue(j) << " "; cout << endl;
		cout << "tangentVector = " << f.tangentVector.hi() << endl;
		cout << "widths = "; for (j=0;j<6;j++) cout << f.w.getValue(j)<<" " << endl;
		cout << "center partials= "; 
		for (j=0;j<6;j++) cout << f.tangentVector.partial(j) << " " << endl;
		cout << "taylorError " << taylorError(f.w,f.DD) << endl << endl;
		}

	}

	/*get min*/{
	int i,j;
	double temp = /*float.h*/DBL_MAX; 
	double Dtemp[6]; for (i=0;i<6;i++) Dtemp[i]= DBL_MAX;
	for (i=0;i<64;i++) 
		{
		domain c = makeDomain(i,xx,zz); 
		lineInterval li = (*G)(c);
		if (temp>li.low()) temp = li.low();
		for (j=0;j<6;j++) if (Dtemp[j]>interMath::inf(li.partial(j)))
			Dtemp[j]=interMath::inf(li.partial(j));
		}
	for (int k=0;k<6;k++) 
	if (!barelyLess(f.lowerPartial(k),Dtemp[k],epsilon))
		{
		cout << "testProc Dmin("<<k<<") failed " << s << endl;
		cout << "found = " << Dtemp[k] << " bounded by = " << 
			f.lowerPartial(k) << endl;
		interMath::up();
		cout << "diff = " << -f.lowerPartial(k) + Dtemp[k] << endl;
		for (j=0;j<6;j++) cout << xx.getValue(j) << " "; cout << endl;
		for (j=0;j<6;j++) cout << zz.getValue(j) << " "; cout << endl;
		}
	if (!barelyLess(f.lowerBound(),temp,epsilon))
		{
		cout << "testProc min failed " << s << endl;
		cout << "found = " << temp << " bounded by = " << f.lowerBound() << endl;
		cout << "diff = " << f.lowerBound() - temp << endl;
		for (j=0;j<6;j++) cout << xx.getValue(j) << " "; cout << endl;
		for (j=0;j<6;j++) cout << zz.getValue(j) << " "; cout << endl;
		}
	}

	}


void taylorFunction::selfTest() 
	{
	cout << " -- loading taylor routines " << endl;
	/*test Proc*/{
	testProcedure(taylorSimplex::x1,lineX1,domain(2,2,2,2,2,2),
		domain(2.51,2.51,2.51,2.51,2.51,2.51),"x1");
	testProcedure(taylorSimplex::dih,linearization::dih,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::dih");
	testProcedure(taylorSimplex::dih2,linearization::dih2,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::dih2");
	testProcedure(taylorSimplex::dih3,linearization::dih3,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::dih3");
	testProcedure(taylorSimplex::sol,linearization::solid,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::sol");
	testProcedure(taylorSimplex::eta2_126,linearization::eta2,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::eta2_126",5.0e-6);
	testProcedure(taylorSimplex::eta2_135,linearization::eta2_135,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::eta2_135",5.0e-6);
	testProcedure(taylorSimplex::eta2_234,linearization::eta2_234,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::eta2_234",5.0e-6);
	testProcedure(taylorSimplex::eta2_456,linearization::eta2_456,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::eta2_456",5.0e-6);

	}
	

	/*test +,*,evalf,evalAt */{
	domain x(4.1,4.2,4.3,4.4,4.5,4.6);
	domain z(4.11,4.22,4.33,4.44,4.55,4.66);
	taylorFunction f = taylorSimplex::x1*"17" + taylorSimplex::x2*"2";
	taylorInterval t = f.evalf(x,z);
	if (!epsilonClose(t.upperBound(),"78.31",1.0e-13))
		cout << " t.upperBound() = " << t.upperBound() << endl;
	if (!epsilonClose(t.lowerBound(),"78.1",1.0e-13))
		cout << " t.lowerBound() = " << t.lowerBound() << endl;
	if (!epsilonClose(t.upperPartial(0),"17",1.0e-15))
		cout << " t.upperPartial(0)= " << t.upperPartial(0) << endl;
	if (!epsilonClose(t.lowerPartial(0),"17",1.0e-15))
		cout << " t.lowerPartial(0)= " << t.lowerPartial(0) << endl;
	if (!epsilonClose(t.upperPartial(1),"2",1.0e-15))
		cout << " t.upperPartial(1)= " << t.upperPartial(1) << endl;
	if (!epsilonClose(t.lowerPartial(1),"2",1.0e-15))
		cout << " t.lowerPartial(1)= " << t.lowerPartial(1) << endl;
	lineInterval L = f.evalAt(x);
	if (!epsilonClose(L.hi(),"78.1",1.0e-13))
		cout << " L.hi() = " << L.hi() << endl;
	if (!epsilonClose(L.low(),"78.1",1.0e-13))
		cout << " L.low() = " << L.low() << endl;
	if (!epsilonClose(17,L.partial(0),1.0e-15))
		cout << " L.partial(0)= " << L.partial(0) << endl;
	if (!epsilonClose(2,L.partial(1),1.0e-15))
		cout << " L.partial(1)= " << L.partial(1) << endl;
	}
	

	/*test plus,scale,center,upperBound,lowerBound,&partials*/ {
	domain x(4.1,4.2,4.3,4.4,4.5,4.6);
	domain z(4.11,4.22,4.33,4.44,4.55,4.66);
	taylorInterval t1 = taylorSimplex::x1.evalf(x,z);
	taylorInterval t2 = taylorSimplex::x2.evalf(x,z);
	taylorInterval s1 = taylorInterval::scale(t1,interval("17"));
	taylorInterval s2 = taylorInterval::scale(t2,interval("2"));
	taylorInterval t = taylorInterval::plus(s1,s2);
	if (!epsilonClose(t.upperBound(),"78.31",1.0e-13))
		cout << " t.upperBound() = " << t.upperBound() << endl;
	if (!epsilonClose(t.lowerBound(),"78.1",1.0e-13))
		cout << " t.lowerBound() = " << t.lowerBound() << endl;
	if (!epsilonClose(t.upperPartial(0),"17",1.0e-15))
		cout << " t.upperPartial(0)= " << t.upperPartial(0) << endl;
	if (!epsilonClose(t.lowerPartial(0),"17",1.0e-15))
		cout << " t.lowerPartial(0)= " << t.lowerPartial(0) << endl;
	if (!epsilonClose(t.upperPartial(1),"2",1.0e-15))
		cout << " t.upperPartial(1)= " << t.upperPartial(1) << endl;
	if (!epsilonClose(t.lowerPartial(1),"2",1.0e-15))
		cout << " t.lowerPartial(1)= " << t.lowerPartial(1) << endl;
	if (!t.isValidData()) cout << "invalid data " << endl;
	lineInterval c = t.tangentVectorOf();
	if (!epsilonClose(c.hi(),"78.205",1.0e-13))
		cout << " c.hi() = " << c.hi() << endl;
	if (!epsilonClose(c.low(),"78.205",1.0e-13))
		cout << " c.low() = " << c.low() << endl;
	if (!epsilonClose(17,c.partial(0),1.0e-15))
		cout << " c.partial(0)= " << c.partial(0) << endl;
	if (!epsilonClose(2,c.partial(1),1.0e-15))
		cout << " c.partial(1)= " << c.partial(1) << endl;
	}
	

	/*test x1*/ {
	int i,j;
	domain x(4.1,4.2,4.3,4.4,4.5,4.6);
	domain z(4.11,4.22,4.33,4.44,4.55,4.66);
	char zz[6][30]={"4.11","4.22","4.33","4.44","4.55","4.66"};
	char xx[6][30]={"4.1","4.2","4.3","4.4","4.5","4.6"};
	for (j=0;j<6;j++) {
	taylorInterval t = taylorSimplex::x1.evalf(x,z);
	switch (j)
		{
		case 0 : t = taylorSimplex::x1.evalf(x,z); break;
		case 1 : t = taylorSimplex::x2.evalf(x,z); break;
		case 2 : t = taylorSimplex::x3.evalf(x,z); break;
		case 3 : t = taylorSimplex::x4.evalf(x,z); break;
		case 4 : t = taylorSimplex::x5.evalf(x,z); break;
		case 5 : t = taylorSimplex::x6.evalf(x,z); break;
		}
	if (!epsilonClose(t.upperBound(),zz[j],1.0e-14))
		cout << "x" << j+1 << "+ fails " << t.upperBound() << endl;
	if (!epsilonClose(t.lowerBound(),xx[j],1.0e-14))
		cout << "x" << j+1 << "- fails " << t.lowerBound() << endl;
	for (i=0;i<6;i++) {
	if (!epsilonClose(t.upperPartial(i),i==j ? "1" : "0",1.0e-15))
		cout << "x" << j+1 << "++ fails " << i 
			<< " " << t.upperPartial(i) << endl;
	if (!epsilonClose(t.lowerPartial(i),i==j ? "1" : "0",1.0e-15))
		cout << "x" << j+1 << "-- fails " << i 
			<< " " << t.lowerPartial(i) << endl;
	}
	}
	}

	/*test y1*/ {
	int i,j;
	domain x(4.1,4.2,4.3,4.4,4.5,4.6);
	domain z(4.11,4.22,4.33,4.44,4.55,4.66);
	char zz[6][30]={"4.11","4.22","4.33","4.44","4.55","4.66"};
	char xx[6][30]={"4.1","4.2","4.3","4.4","4.5","4.6"};
	for (j=0;j<6;j++) {
	taylorInterval t = taylorSimplex::x1.evalf(x,z);
	switch (j)
		{
		case 0 : t = taylorSimplex::y1.evalf(x,z); break;
		case 1 : t = taylorSimplex::y2.evalf(x,z); break;
		case 2 : t = taylorSimplex::y3.evalf(x,z); break;
		case 3 : t = taylorSimplex::y4.evalf(x,z); break;
		case 4 : t = taylorSimplex::y5.evalf(x,z); break;
		case 5 : t = taylorSimplex::y6.evalf(x,z); break;
		}
	if (!epsilonClose(t.upperBound(),interMath::sqrt(interval(zz[j])),1.0e-4))
		cout << "x" << j+1 << "+ fails " << t.upperBound() << endl;
	if (!epsilonClose(t.lowerBound(),interMath::sqrt(interval(xx[j])),1.0e-5))
		cout << "x" << j+1 << "- fails " << t.lowerBound() << endl;
	static interval half("0.5");
	for (i=0;i<6;i++) {
	if (!epsilonClose(t.upperPartial(i),i==j ? 
		half/interMath::sqrt(interval(xx[j])) : interval("0"),1.0e-5))
		cout << "x" << j+1 << "++ fails " << i 
			<< " " << t.upperPartial(i) << endl;
	if (!epsilonClose(t.lowerPartial(i),i==j ? 
		half/interMath::sqrt(interval(zz[j])) : interval("0"),1.0e-4))
		cout << "x" << j+1 << "-- fails " << i 
			<< " " << t.lowerPartial(i) << endl;
	}
	}
	}

	/*test unit*/ {
	domain x(4.1,4.2,4.3,4.4,4.5,4.6);
	domain z(4.11,4.22,4.33,4.44,4.55,4.66);
	taylorInterval t = taylorSimplex::unit.evalf(x,z);
	if ((!t.upperBound()==1) || (!t.lowerBound()==1))
		cout << "unit fails = " << t.upperBound()<<" " << t.lowerBound()<<endl;
	for (int i=0;i<6;i++) if ((t.upperPartial(i)!=0)||(t.lowerPartial(i)!=0))
		cout << "unitp fails = " << t.upperPartial(i)<<" " << t.lowerPartial(i)<<endl;
	}

	/* test hasDeltaDenom */ {
	  taylorFunction F1 = taylorSimplex::y1 + taylorSimplex::dih2;
	  if (!F1.hasDeltaDenom()) cout << "hasDeltaDenom fails 1" << endl;
	  taylorFunction F2 (taylorSimplex::y2);
	  if (F2.hasDeltaDenom()) cout << "hasDeltaDenom fails 2" << endl;
	  taylorFunction F3( taylorSimplex::dih);
	  if (!F3.hasDeltaDenom()) cout << "hasDeltaDenom fails 3" << endl;
	}

	/* compositeData */ {
	  compositeData cD (&taylorSimplex::dih,
			    &taylorSimplex::x2,&taylorSimplex::x3,&taylorSimplex::x1,
			    &taylorSimplex::x5,&taylorSimplex::x6,&taylorSimplex::x4,NULL);
	  domain x(4.1,4.2,4.3,4.4,4.5,4.6);
	  domain w(0.0,0.0,0.0,0.0,0.0,0.0);
          taylorInterval t = cD.evalf(w,x,x,x); //dih2alt
	  taylorInterval u = taylorSimplex::dih2.evalf4(w,x,x,x);
	  if (!epsilonClose(t.upperBound(),u.tangentVectorOf().f,1.0e-8))
	  cout << "cD  fails " << t.upperBound() << endl;
	  if (!epsilonClose(t.lowerBound(),u.tangentVectorOf().f,1.0e-8))
		cout << "cD fails lB "  << t.lowerBound() << endl;
	for (int i=0;i<6;i++) {
	  if (!epsilonClose(t.upperPartial(i),u.tangentVectorOf().Df[i],1.0e-15))
	    cout << "cD " << i << "++ fails " << t.upperPartial(i) << endl;
	  if (!epsilonClose(t.lowerPartial(i),u.tangentVectorOf().Df[i],1.0e-15))
		cout << "cDl fails " << i 	<< " " << t.lowerPartial(i) << endl;
	}
	}

	/*
	cout << " -- not tested :  " <<
		" \n      taylorInterval::upper/lowerboundQ \n";
	*/

}
