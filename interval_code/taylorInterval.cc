#include <iomanip.h>
#include <math.h>
#include <time.h>
#include <stdlib.h>
#include <float.h>
#include "interval.h"
#include "lineInterval.h"
#include "secondDerive.h"
#include "taylorInterval.h"

class primitive
{
private:
	lineInterval (*hfn)(const domain&);
	int (*setSecond)(const domain& x,const domain& z,double [6][6]);
public:
	lineInterval center(const domain& x) { return (*hfn)(x); }
	taylorInterval evalf(const domain& w,const domain& x,
		const domain& y,const domain& z) const;
	primitive(lineInterval (*)(const domain& ),
		int (*)(const domain& ,const domain&,double [6][6]));
};

class details 
{
public:
    primPtr* basisVector;
    interval* basisCoeff;
    int basisCount;
    int basisCapacity;
	details(int capacity) { 
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


taylorInterval primitive::evalf
	(const domain& w,const domain& x,const domain& y,const domain& z) const
	{
	double DD[6][6];
	int s = (*setSecond)(x,z,DD);
	lineInterval centerPoint = (*hfn)(y);
	return taylorInterval(s,centerPoint,w,DD);
	}

static inline double max(double x,double y)
	{ return (x>y ? x : y); }

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
        temp = X->basisVector[i]->center(x);
		c = X->basisCoeff[i];
		total.f = total.f + c*temp.f;
		for (j=0;j<6;j++)
		total.Df[j]= total.Df[j]+ c*temp.Df[j];
		}
    return total;
	}

primitive::primitive(lineInterval (*hfn0)(const domain&),
	int (*setSecond0)(const domain&,const domain&,double [6][6]))
	{
	hfn = hfn0;
	setSecond = setSecond0;
	}

static inline double dabs(interval x)
    {
    return interMath::sup(interMath::max(x,-x));
    }

taylorInterval::taylorInterval(int s,const lineInterval& h0,
	const domain& w0,const double DD0[6][6])
	{
	w = w0;
	int i,j;
	validDataFlag = s;
	centerPoint = h0;
	if (s) for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=DD0[i][j];
	}

int taylorInterval::isValidData() const
	{ return validDataFlag; }

lineInterval taylorInterval::center() const
	{
	static const interval zero("0");
	if (!validDataFlag) 
		{ error::message("center computation failed"); 
		  return lineInterval(zero); }
	return centerPoint;
	}

static double taylorError(const domain& w,const double sec[6][6])
    {
    interMath::up();
    double t=0.0;
    int i,j;
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
    double t = centerPoint.hi() + err;
    for (int i=0;i<6;i++) t = t+ w.getValue(i)*dabs(centerPoint.partial(i));
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
    double t = centerPoint.low() - err;
    for (int i=0;i<6;i++) t = t + (-w.getValue(i))*dabs(centerPoint.partial(i));
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
    double t = cA.centerPoint.hi()+cB.centerPoint.hi() + err;
    int k[3]={0,4,5},i;
    for (i=0;i<3;i++) t = 
		t+ cA.w.getValue(k[i])*dabs(cA.center().partial(k[i]));
    for (i=0;i<3;i++) t = 
		t+ cB.w.getValue(k[i])*dabs(cB.center().partial(k[i]));
    for (i=1;i<4;i++) t = t+ cB.w.getValue(i)*
		dabs(cB.center().partial(i)+cA.center().partial(i));
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
    double t = cA.centerPoint.low()+cB.centerPoint.low() - err;
    int k[3]={0,4,5},i;
    for (i=0;i<3;i++) t = t+ 
		(-cA.w.getValue(k[i]))*dabs(cA.center().partial(k[i]));
    for (i=0;i<3;i++) t = t+ 
		(-cB.w.getValue(k[i]))*dabs(cB.center().partial(k[i]));
    for (i=1;i<4;i++) t = t+ (-cB.w.getValue(i))
		*dabs(cB.center().partial(i)+cA.center().partial(i));
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
	return interMath::sup(centerPoint.partial(i)) + err;
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
	return interMath::inf(centerPoint.partial(i)) - err;
	}

static void intervalToDouble(interval DDx[6][6],double DD[6][6])
	{
	for (int i=0;i<6;i++) for (int j=0;j<6;j++)
		DD[i][j]= interMath::sup(interMath::max(DDx[i][j],-DDx[i][j]));
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

/*implement dih1*/
static int setDihedral(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
	int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	return secondDerive::setDihedral(X,Z,DD);
	}
primitive dih1(linearization::dih,setDihedral);
const taylorFunction taylorSimplex::dih(::dih1);

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
primitive dih2(linearization::dih2,setDih2);
const taylorFunction taylorSimplex::dih2(::dih2);

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
primitive dih3(linearization::dih3,setDih3);
const taylorFunction taylorSimplex::dih3(::dih3);

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
primitive sol(linearization::solid,setSol);
const taylorFunction taylorSimplex::sol(::sol);

/*implement vorAnalytic */
static int setVorAnalytic(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
    int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	return secondDerive::setVorAnalytic(X,Z,DD);
	}
primitive vor(linearization::vorAnalytic,setVorAnalytic);
const taylorFunction taylorSimplex::vor(::vor);

/*implement quo*/
static int setQuo(const domain& ,const domain& ,double DD[6][6])
	{
	int i,j;
	for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=0;
	int k[3]={0,1,5};
	// see SECOUT/out.quoin.simplex.1255. Max absolute value is 0.0062144...
	for (i=0;i<3;i++) for (j=0;j<3;j++) DD[k[i]][k[j]]= 0.007;
	return 1;
	}
static primitive quo(linearization::quo,setQuo);
const taylorFunction taylorQrtet::quo(::quo);

/*implement lowVorVc*/
static int setLowVorVc(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
    int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	return secondDerive::setVorVc(X,Z,DD);
	}
static primitive lowVc(linearization::VorVc,setLowVorVc);
const taylorFunction taylorSimplex::lowVorVc(::lowVc);

/*implement vorSqc*/
static int setVorSqc(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
    int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	return secondDerive::setVorSqc(X,Z,DD);
	}
static primitive Sqc(linearization::VorSqc,setVorSqc);
const taylorFunction taylorSimplex::vorSqc(::Sqc);

/*implement vor1385*/
static int setVor1385(const domain& x,const domain& z,double DD[6][6])
	{
	double X[6],Z[6];
    int i;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
	return secondDerive::setVor1385(X,Z,DD);
	}
static primitive V1385(linearization::Vor1385,setVor1385);
const taylorFunction taylorFlat::vor1385(::V1385);

static int copy(double DD[6][6],const double sec[6][6])
    {
    for (int i=0;i<6;i++) for (int j=0;j<6;j++)
        DD[i][j]=sec[i][j];
    return 1;
    }

/************************* QRTET FUNCTIONS ******************************/
/*implement gammaQR*/
static int setGammaQR(const domain&,const domain&,double DD[6][6])
	{
	static const double gamsecq[6][6]=
      {{0.1505081218334406, 0.0987415739454046, 0.0987415739454046,
    0.0904416359075526, 0.0989502641265695, 0.0989502641265695},
   {0.0987415739454046, 0.1472361623948175, 0.0972711666314722,
    0.0972711666314722, 0.0899978329092247, 0.0980605035191848},
   {0.0987415739454046, 0.0972711666314722, 0.1472361623948175,
    0.0972711666314722, 0.0980605035191848, 0.0899978329092247},
   {0.0904416359075526, 0.0972711666314722, 0.0972711666314722,
    0.1472361623948175, 0.0980605035191848, 0.0980605035191848},
   {0.0989502641265695, 0.0899978329092247, 0.0980605035191848,
    0.0980605035191848, 0.1483489164399885, 0.0976885469938018},
   {0.0989502641265695, 0.0980605035191848, 0.0899978329092247,
    0.0980605035191848, 0.0976885469938018, 0.1483489164399885}};
	return copy(DD,gamsecq);
	}
primitive gammaQR(linearization::gamma,setGammaQR);
const taylorFunction taylorQrtet::gamma(::gammaQR);

/*implement vorAnalyticQR*/
static int setVorAnalyticQR(const domain&,const domain&,double DD[6][6])
	{
	static const double vorsecq[6][6]=
	{{0.4764018743941502, 0.331659346562304, 0.331659346562304,
    0.21298711106907, 0.2569456978991421, 0.2569456978991421},
   {0.331659346562304, 0.4642103520429511, 0.3189822170847934,
    0.2518613355451742, 0.2130737168159708, 0.2518613355451746},
   {0.331659346562304, 0.3189822170847934, 0.4642103520429511,
    0.2518613355451742, 0.2518613355451746, 0.2130737168159708},
   {0.21298711106907, 0.2518613355451742, 0.2518613355451742,
    0.2378845709065222, 0.1907110592742963, 0.1907110592742963},
   {0.2569456978991421, 0.2130737168159708, 0.2518613355451746,
    0.1907110592742963, 0.2378845709065225, 0.1997072630942962},
   {0.2569456978991421, 0.2518613355451746, 0.2130737168159708,
    0.1907110592742963, 0.1997072630942962, 0.2378845709065225}};
	return copy(DD,vorsecq);
	}
primitive vorAnalyticQR(linearization::vorAnalytic,setVorAnalyticQR);
const taylorFunction taylorQrtet::vor(::vorAnalyticQR);

/*implement solidQR*/
static int setSolidQR(const domain&,const domain&,double DD[6][6])
    {
	static const double solsecq[6][6]=
     {{0.1008221003655132, 0.1001966108010378, 0.1001966108010378,
    0.04170470709398239, 0.03597275361874876, 0.03597275361874876},
   {0.1001966108010378, 0.0974838382300004, 0.0978286001379002,
    0.03534668307525432, 0.04101049501981311, 0.03534668307525433},
   {0.1001966108010378, 0.0978286001379002, 0.0974838382300004,
    0.03534668307525432, 0.03534668307525433, 0.04101049501981311},
   {0.04170470709398239, 0.03534668307525432, 0.03534668307525432,
    0.03468054377737053, 0.03085232133983355, 0.03085232133983355},
   {0.03597275361874876, 0.04101049501981311, 0.03534668307525433,
    0.03085232133983355, 0.0346805437773705, 0.03085232133983355},
   {0.03597275361874876, 0.03534668307525433, 0.04101049501981311,
    0.03085232133983355, 0.03085232133983355, 0.0346805437773705}};
	return copy(DD,solsecq);
	}
primitive solidQR(linearization::solid,setSolidQR);
const taylorFunction taylorQrtet::sol(::solidQR);

/*implement rad2QR*/
static int setRad2QR(const domain& x,const domain& z,double DD[6][6])
	{
    // chi^2/(4 u delta) + eta^2 = rad^2;
    // bound on eta2 computed in SECOUT/out.eta2
	double X[6],Z[6];
	int i,j;
	for (i=0;i<6;i++) { X[i]=x.getValue(i); Z[i]=z.getValue(i); }
    static const double XX = 0.04;
    static const int k[3] = {0,1,5};
	if (!secondDerive::setChi2over4uDelta(X,Z,DD)) return 0;
    interMath::up();
	for (i=0;i<3;i++) for (j=0;j<3;j++)
	DD[k[i]][k[j]]= DD[k[i]][k[j]]+ XX;
    return 1;
	}
primitive rad2QR(linearization::rad2,setRad2QR);
const taylorFunction taylorQrtet::rad2(::rad2QR);

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
primitive eta2(linearization::eta2,setEta2_126);
const taylorFunction taylorSimplex::eta2_126(::eta2);

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
primitive Peta2_135(linearization::eta2_135,setEta2_135);
const taylorFunction taylorSimplex::eta2_135(::Peta2_135);

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
primitive Peta2_234(linearization::eta2_234,setEta2_234);
const taylorFunction taylorSimplex::eta2_234(::Peta2_234);

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



/*implement dihQR*/
static const double dihsecq[6][6]=
      {{0.05615705015025188, 0.05954781700907451, 0.05954781700907451,
    0.05135019867517077, 0.05954781700907451, 0.05954781700907451},
   {0.05954781700907451, 0.06197838551869915, 0.0742743789801271,
    0.04627781366683503, 0.04075662992838126, 0.05212400198046736},
   {0.05954781700907451, 0.0742743789801271, 0.06197838551869915,
    0.04627781366683503, 0.05212400198046736, 0.04075662992838126},
   {0.05135019867517077, 0.04627781366683503, 0.04627781366683503,
    0.03592041571837889, 0.04974975917075734, 0.04974975917075734},
   {0.05954781700907451, 0.04075662992838126, 0.05212400198046736,
    0.04974975917075734, 0.06197838551869915, 0.07427437898012714},
   {0.05954781700907451, 0.05212400198046736, 0.04075662992838126,
    0.04974975917075734, 0.07427437898012714, 0.06197838551869915}};
static int setDihQR(const domain&,const domain&,double DD[6][6])
    {
	return copy(DD,dihsecq);
	}
primitive dihQR(linearization::dih,setDihQR);
const taylorFunction taylorQrtet::dih(::dihQR);

static int setDih2QR(const domain&,const domain&,double DD[6][6])
    {
    int k[6]={1,0,2,4,3,5};
    for (int i=0;i<6;i++) for (int j=0;j<6;j++)
        DD[i][j]= dihsecq[k[i]][k[j]];
    return 1;
    }
primitive dih2QR(linearization::dih2,setDih2QR);
const taylorFunction taylorQrtet::dih2(::dih2QR);

static int setDih3QR(const domain&,const domain&,double DD[6][6])
    {
    int k[6]={2,1,0,5,4,3};
    for (int i=0;i<6;i++) for (int j=0;j<6;j++)
        DD[i][j]= dihsecq[k[i]][k[j]];
    return 1;
    }
primitive dih3QR(linearization::dih3,setDih3QR);
const taylorFunction taylorQrtet::dih3(::dih3QR);

/************************* FLAT FUNCTIONS ******************************/
/*implement gammaF*/
static int setGammaF(const domain&,const domain&,double DD[6][6])
	{
	static const double gamsecf[6][6]=
      {{0.2328615196697771, 0.1855111040967506, 0.1855111040967506,
    0.1854394137033798, 0.1855111040967506, 0.1855111040967506},
   {0.1855111040967506, 0.2208078073704518, 0.1670368118212323,
    0.1709276028978653, 0.1222038974472753, 0.1520276586955859},
   {0.1855111040967506, 0.1670368118212323, 0.2208078073704518,
    0.1709276028978653, 0.1520276586955859, 0.1222038974472753},
   {0.1854394137033798, 0.1709276028978653, 0.1709276028978653,
    0.1796647854805246, 0.1709276028978653, 0.1709276028978653},
   {0.1855111040967506, 0.1222038974472753, 0.1520276586955859,
    0.1709276028978653, 0.2208078073704518, 0.1670368118212323},
   {0.1855111040967506, 0.1520276586955859, 0.1222038974472753,
    0.1709276028978653, 0.1670368118212323, 0.2208078073704518}};
	return copy(DD,gamsecf);
	}
primitive gammaF(linearization::gamma,setGammaF);
const taylorFunction taylorFlat::gamma(::gammaF);

/*implement vorAnalyticF*/
static int setVorAnalyticF(const domain&,const domain&,double DD[6][6])
	{
	static const double vorsecf[6][6]= 
	{{0.4667858608452715, 0.548215749659522, 0.548215749659522,
    0.3543884477421286, 0.4340960290926191, 0.4340960290926191},
   {0.548215749659522, 0.7416603405713062, 0.6544254881497676,
    0.4297356554522379, 0.4700440458574503, 0.5336426912566655},
   {0.548215749659522, 0.6544254881497676, 0.7416603405713062,
    0.4297356554522379, 0.5336426912566655, 0.4700440458574503},
   {0.3543884477421286, 0.4297356554522379, 0.4297356554522379,
    0.515880504594417, 0.4687480083372963, 0.4687480083372963},
   {0.4340960290926191, 0.4700440458574503, 0.5336426912566655,
    0.4687480083372963, 0.5353733609797348, 0.4451072893510121},
   {0.4340960290926191, 0.5336426912566655, 0.4700440458574503,
    0.4687480083372963, 0.4451072893510121, 0.5353733609797348}};
	return copy(DD,vorsecf);
	}
primitive vorAnalyticF(linearization::vorAnalytic,setVorAnalyticF);
const taylorFunction taylorFlat::vor(::vorAnalyticF);

/*implement solidF*/
static int setSolidF(const domain&,const domain&,double DD[6][6])
	{
	static const double solsecf[6][6]=
  {{0.04371155939967812, 0.07916064652631018, 0.07916064652631018,
    0.0603529187865793, 0.03769056080178152, 0.03769056080178152},
   {0.07916064652631018, 0.0871215068555988, 0.07271729668978311,
    0.06570022301527903, 0.04820917216443769, 0.0637099938590001},
   {0.07916064652631018, 0.07271729668978311, 0.0871215068555988,
    0.06570022301527903, 0.0637099938590001, 0.04820917216443769},
   {0.0603529187865793, 0.06570022301527903, 0.06570022301527903,
    0.06899272510468771, 0.05543073847641561, 0.05543073847641561},
   {0.03769056080178152, 0.04820917216443769, 0.0637099938590001,
    0.05543073847641561, 0.05715793121958739, 0.03250602234159555},
   {0.03769056080178152, 0.0637099938590001, 0.04820917216443769,
    0.05543073847641561, 0.03250602234159555, 0.05715793121958739}};
	return copy(DD,solsecf);
	}
primitive solidF(linearization::solid,setSolidF);
const taylorFunction taylorFlat::sol(::solidF);

/*implement dihF*/
static int setDihF(const domain&,const domain&,double DD[6][6])
	{
	static const double dihsecf[6][6]= 
		// scaled by 1.3 from SECOUT/..sec.F:DIHf.
      {{0.1371343611737817, 0.149151795097861, 0.149151795097861,
    0.1273324155461821, 0.149151795097861, 0.149151795097861},
   {0.149151795097861, 0.1595285638511244, 0.1560411887442528,
    0.1162997089898195, 0.0993520398363286, 0.1305530477917785},
   {0.149151795097861, 0.1560411887442528, 0.1595285638511244,
    0.1162997089898195, 0.1305530477917785, 0.0993520398363286},
   {0.1273324155461821, 0.1162997089898195, 0.1162997089898195,
    0.0827475622584163, 0.1216060002379419, 0.1216060002379419},
   {0.149151795097861, 0.0993520398363286, 0.1305530477917785,
    0.1216060002379419, 0.1595285638511244, 0.1560411887442529},
   {0.149151795097861, 0.1305530477917785, 0.0993520398363286,
    0.1216060002379419, 0.1560411887442529, 0.1595285638511244}};
	return copy(DD,dihsecf);
	}
primitive dihF(linearization::dih,setDihF);
const taylorFunction taylorFlat::dih(::dihF);


static const double dih2secf[6][6] =// Sc[DIH2f]= (updated 4/5/97)
     {{0.0866641704247729, 0.111953793126292, 0.1348380593047117,
    0.0995680672164788, 0.07673812070208658, 0.110270246493761},
   {0.111953793126292, 0.1506142217431531, 0.1352723298502763,
    0.1021232978892872, 0.06864316838329634, 0.1254130397993319},
   {0.1348380593047117, 0.1352723298502763, 0.1421190843523113,
    0.1037352281264406, 0.0960127830707552, 0.101973644747935},
   {0.0995680672164788, 0.1021232978892872, 0.1037352281264406,
    0.0853458268382053, 0.0801690053219753, 0.1223072946085182},
   {0.07673812070208658, 0.06864316838329634, 0.0960127830707552,
    0.0801690053219753, 0.0946617011988348, 0.0986654632788401},
   {0.110270246493761, 0.1254130397993319, 0.101973644747935,
    0.1223072946085182, 0.0986654632788401, 0.137920585495589}};
static int setDih2F(const domain&,const domain&,double DD[6][6])
	{
	return copy(DD,dih2secf);
	}
primitive dih2F(linearization::dih2,setDih2F);
const taylorFunction taylorFlat::dih2(::dih2F);

static int setDih3F(const domain&,const domain&,double DD[6][6])
	{
    int k[6]={0,2,1,3,5,4};
    for (int i=0;i<6;i++) for (int j=0;j<6;j++)
        DD[i][j]= dih2secf[k[i]][k[j]]; // changed form dihsecf 11/1/97.
    return 1;
    }
primitive dih3F(linearization::dih3,setDih3F);
const taylorFunction taylorFlat::dih3(::dih3F);


/************************* UPRIGHT FUNCTIONS ******************************/
/*implement gammaU*/
static int setGammaU(const domain&,const domain&,double DD[6][6])
	{
	static const double gamsecu[6][6]=
      {{0.1815102008803288, 0.1721285491194339, 0.1721285491194339,
    0.1853730180004061, 0.1721285491194339, 0.1721285491194339},
   {0.1721285491194339, 0.2208078073704521, 0.152027658695586,
    0.1843101578751823, 0.1222038974472756, 0.1670368118212326},
   {0.1721285491194339, 0.152027658695586, 0.2208078073704521,
    0.1843101578751823, 0.1670368118212326, 0.1222038974472756},
   {0.1853730180004061, 0.1843101578751823, 0.1843101578751823,
    0.2311488956759207, 0.1843101578751823, 0.1843101578751823},
   {0.1721285491194339, 0.1222038974472756, 0.1670368118212326,
    0.1843101578751823, 0.2208078073704521, 0.1520276586955861},
   {0.1721285491194339, 0.1670368118212326, 0.1222038974472756,
    0.1843101578751823, 0.1520276586955861, 0.2208078073704521}};
	return copy(DD,gamsecu);
	}
primitive gammaU(linearization::gamma,setGammaU);
const taylorFunction taylorUpright::gamma(::gammaU);

/*implement vorAnalytic*/
static int setVorAnalyticU(const domain&,const domain&,double DD[6][6])
	{
	static const double vorsecu[6][6]=  
	{{0.4281487180299025, 0.5849864343593457, 0.5849864343593457,
    0.349067754637769, 0.5565204830263398, 0.5565204830263398},
   {0.5849864343593457, 0.6525017708105887, 0.5686451859032814,
    0.3123580298119767, 0.4792689926768498, 0.4981758511336457},
   {0.5849864343593457, 0.5686451859032814, 0.6525017708105887,
    0.3123580298119767, 0.4981758511336457, 0.4792689926768498},
   {0.349067754637769, 0.3123580298119767, 0.3123580298119767,
    0.2264624414472072, 0.2174821857633429, 0.2174821857633429},
   {0.5565204830263398, 0.4792689926768498, 0.4981758511336457,
    0.2174821857633429, 0.4622578807953082, 0.4831762324598516},
   {0.5565204830263398, 0.4981758511336457, 0.4792689926768498,
    0.2174821857633429, 0.4831762324598516, 0.4622578807953082}};
	return copy(DD,vorsecu);
	}
primitive vorAnalyticU(linearization::vorAnalytic,setVorAnalyticU);
const taylorFunction taylorUpright::vor(::vorAnalyticU);

/*implement vorVcU*/
static int setVorVcU(const domain&,const domain&,double DD[6][6])
	{
	static const double vorVcsecu[6][6]= // Sc[Vc]=
    {{0.1782227307193559, 0.131733343537643, 0.131733343537643,
    0.0921731861203008, 0.07792820729509741, 0.07792820729509741},
   {0.131733343537643, 0.2049667790628317, 0.1441228966927744,
    0.1174938110075899, 0.0875545068468916, 0.095864100034125},
   {0.131733343537643, 0.1441228966927744, 0.2049667790628317,
    0.1174938110075899, 0.095864100034125, 0.0875545068468916},
   {0.0921731861203008, 0.1174938110075899, 0.1174938110075899,
    0.0833074490709164, 0.06820300088610705, 0.06820300088610705},
   {0.07792820729509741, 0.0875545068468916, 0.095864100034125,
    0.06820300088610705, 0.07517458966537904, 0.05616291825796102},
   {0.07792820729509741, 0.095864100034125, 0.0875545068468916,
    0.06820300088610705, 0.05616291825796102, 0.07517458966537904}};
	return copy(DD,vorVcsecu);
	}
primitive vorVcU(linearization::uprightVorVc,setVorVcU);
const taylorFunction taylorUpright::vorVc(::vorVcU);

/*implement taylorSimplex::highVorVc*/
static int setHighVorVc(const domain&x,const domain&z,double DD[6][6])
	{	
	double tx[6],tz[6];
	for (int i=0;i<6;i++) { tx[i]=x.getValue(i); tz[i]=z.getValue(i); }
	return secondDerive::setVorVc(tx,tz,DD);
	}
primitive highVorVc(linearization::uprightVorVc,setHighVorVc);
const taylorFunction taylorSimplex::highVorVc(::highVorVc);

/*implement solU */
static int setSolidU(const domain&,const domain&,double DD[6][6])
	{
	static const double solsecu[6][6]=
      {{0.04371155939967812, 0.07916064652631018, 0.07916064652631018,
    0.0603529187865793, 0.03769056080178152, 0.03769056080178152},
   {0.07916064652631018, 0.0871215068555988, 0.07271729668978311,
    0.06570022301527903, 0.04820917216443769, 0.0637099938590001},
   {0.07916064652631018, 0.07271729668978311, 0.0871215068555988,
    0.06570022301527903, 0.0637099938590001, 0.04820917216443769},
   {0.0603529187865793, 0.06570022301527903, 0.06570022301527903,
    0.06899272510468771, 0.05543073847641561, 0.05543073847641561},
   {0.03769056080178152, 0.04820917216443769, 0.0637099938590001,
    0.05543073847641561, 0.05715793121958739, 0.03250602234159555},
   {0.03769056080178152, 0.0637099938590001, 0.04820917216443769,
    0.05543073847641561, 0.03250602234159555, 0.05715793121958739}};
	return copy(DD,solsecu);
	}
primitive solU(linearization::solid,setSolidU);
const taylorFunction taylorUpright::sol(::solU);

/*implement dihU */
static int setDihU(const domain&,const domain&,double DD[6][6])
	{
	static const double dihsecu[6][6]= 
	// scaled by 1.3 from SECOUT/..sec.U:DIHu.
      {{0.1450836193962311, 0.1736955268004009, 0.1736955268004009,
    0.145991732400618, 0.1736955268004009, 0.1736955268004009},
   {0.1736955268004009, 0.1828764947216819, 0.17708957643007,
    0.1362446891095055, 0.1250091320874734, 0.1632783546843728},
   {0.1736955268004009, 0.17708957643007, 0.1828764947216819,
    0.1362446891095055, 0.1632783546843728, 0.1250091320874734},
   {0.145991732400618, 0.1362446891095055, 0.1362446891095055,
    0.089061331879941, 0.1405282551255984, 0.1405282551255984},
   {0.1736955268004009, 0.1250091320874734, 0.1632783546843728,
    0.1405282551255984, 0.1828764947216819, 0.1770895764300701},
   {0.1736955268004009, 0.1632783546843728, 0.1250091320874734,
    0.1405282551255984, 0.1770895764300701, 0.1828764947216819}};
	return copy(DD,dihsecu);
	}
primitive dihU(linearization::dih,setDihU);
const taylorFunction taylorUpright::dih(::dihU);

/*implement dih2U */
static const double dih2secu[6][6]= // Sc[DIH2u]=  (updated 4/3/97)
     {{0.0870588345543171, 0.1040770926934109, 0.1241944881406908,
    0.1033345528534029, 0.0805005544907577, 0.1178349703632916},
   {0.1040770926934109, 0.1506142217431533, 0.1254130397993321,
    0.1099999983221686, 0.06864316838329656, 0.1352723298502765},
   {0.1241944881406908, 0.1254130397993321, 0.1379205854955892,
    0.1021420651987885, 0.0958952636383356, 0.1044244179653125},
   {0.1033345528534029, 0.1099999983221686, 0.1021420651987885,
    0.0849465464054507, 0.07926035097080792, 0.1326754368537853},
   {0.0805005544907577, 0.06864316838329656, 0.0958952636383356,
    0.07926035097080792, 0.0946617011988349, 0.1005169535734457},
   {0.1178349703632916, 0.1352723298502765, 0.1044244179653125,
    0.1326754368537853, 0.1005169535734457, 0.1421190843523115}};
static int setDih2U(const domain&,const domain&,double DD[6][6])
	{
    return copy(DD,dih2secu);
    }
primitive dih2U(linearization::dih2,setDih2U);
const taylorFunction taylorUpright::dih2(::dih2U);


/*implement dih3U */
static int setDih3U(const domain&,const domain&,double DD[6][6])
	{
    int k[6]={0,2,1,3,5,4};
    for (int i=0;i<6;i++) for (int j=0;j<6;j++)
        DD[i][j]= dih2secu[k[i]][k[j]];
    return 1;
    }
primitive dih3U(linearization::dih3,setDih3U);
const taylorFunction taylorUpright::dih3(::dih3U);

/*implement swapVorU */
static int setSwapVorU(const domain& x,const domain& z,double DD[6][6])
	{
	int k[6]={0,5,4,3,2,1};
	double xx[6],zz[6];
	double DDxz[6][6];
	int i,j;
	for (i=0;i<6;i++) { xx[i]=x.getValue(k[i]); zz[i]=z.getValue(k[i]); }
	domain X(xx[0],xx[1],xx[2],xx[3],xx[4],xx[5]),
		Z(zz[0],zz[1],zz[2],zz[3],zz[4],zz[5]);
	if (!setVorAnalyticU(X,Z,DDxz)) return 0;
	for (i=0;i<6;i++) for (j=0;j<6;j++) DD[k[i]][k[j]]=DDxz[i][j];
	return 1;
	}
primitive swapVorAnalyticU(linearization::VorInverted,setSwapVorU);
const taylorFunction taylorUpright::swapVor(::swapVorAnalyticU);

const taylorFunction taylorUpright::octavor =
	(taylorUpright::swapVor+taylorUpright::vor)*"0.5";

/*implement swapVorVcU */
static int setSwapVorVcU(const domain& x,const domain& z,double DD[6][6])
	{
	double xx[6],zz[6],DDxz[6][6];
	int i,j;
	int k[6]={0,5,4,3,2,1};
	for (i=0;i<6;i++) { xx[i]=x.getValue(k[i]); zz[i]=z.getValue(k[i]); }
	domain X(xx[0],xx[1],xx[2],xx[3],xx[4],xx[5]),
		Z(zz[0],zz[1],zz[2],zz[3],zz[4],zz[5]);
	if (!setVorVcU(X,Z,DDxz)) return 0;
	for (i=0;i<6;i++) for (j=0;j<6;j++) DD[i][j]=DDxz[k[i]][k[j]];
	return 1;
	}
primitive swapVorVcU(linearization::uprightVorVcInverted,setSwapVorVcU);
const taylorFunction taylorUpright::swapVorVc(::swapVorVcU);



/******************** MORE GENERAL STUFF **************************/


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
	s.f = t1.centerPoint.f + t2.centerPoint.f;
	for (i=0;i<6;i++) s.Df[i]= t1.centerPoint.Df[i]+ t2.centerPoint.Df[i];
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
	lineInterval s = t1.centerPoint;
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
		cout << "centerPoint = " << f.centerPoint.hi() << endl;
		cout << "widths = "; for (j=0;j<6;j++) cout << f.w.getValue(j)<<" " << endl;
		cout << "center partials= "; 
		for (j=0;j<6;j++) cout << f.centerPoint.partial(j) << " " << endl;
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
	cout << " -- loading taylor routines $Revision: 1.6 $ " << endl;
	/*test Proc*/{
	testProcedure(taylorSimplex::x1,lineX1,domain(2,2,2,2,2,2),
		domain(2.51,2.51,2.51,2.51,2.51,2.51),"x1");
	testProcedure(taylorSimplex::vor,linearization::vorAnalytic,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::vor");
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
	testProcedure(taylorSimplex::lowVorVc,linearization::VorVc,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::lowVorVc",5.0e-6);
	testProcedure(taylorSimplex::highVorVc,linearization::uprightVorVc,
		domain(6.3001,4,4,4,4,4), domain(8,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::highVorVc",5.0e-6);
	testProcedure(taylorSimplex::vorSqc,linearization::VorSqc,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorSimplex::vorSqc",5.0e-5);
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

	testProcedure(taylorQrtet::dih,linearization::dih,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorQrtet::dih",5.0e-6);
	testProcedure(taylorQrtet::dih2,linearization::dih2,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorQrtet::dih2",5.0e-6);
	testProcedure(taylorQrtet::dih3,linearization::dih3,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorQrtet::dih3",5.0e-6);
	testProcedure(taylorQrtet::sol,linearization::solid,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorQrtet::sol",5.0e-6);
	testProcedure(taylorQrtet::rad2,linearization::rad2,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorQrtet::rad2",1.0e-6);
	testProcedure(taylorQrtet::gamma,linearization::gamma,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorQrtet::gamma",5.0e-6);
	testProcedure(taylorQrtet::vor,linearization::vorAnalytic,
		domain(4,4,4,4,4,4), domain(6.3001,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorQrtet::vor",1.0e-5);

	testProcedure(taylorFlat::dih,linearization::dih,
		domain(4,4,4,6.3001,4,4), domain(6.3001,6.3001,6.3001,8,6.3001,6.3001),
		"taylorFlat::dih",5.0e-6);
	testProcedure(taylorFlat::dih2,linearization::dih2,
		domain(4,4,4,6.3001,4,4), domain(6.3001,6.3001,6.3001,8,6.3001,6.3001),
		"taylorFlat::dih2",5.0e-6);
	testProcedure(taylorFlat::dih3,linearization::dih3,
		domain(4,4,4,6.3001,4,4), domain(6.3001,6.3001,6.3001,8,6.3001,6.3001),
		"taylorFlat::dih3",5.0e-6);
	testProcedure(taylorFlat::sol,linearization::solid,
		domain(4,4,4,6.3001,4,4), domain(6.3001,6.3001,6.3001,8,6.3001,6.3001),
		"taylorFlat::sol",5.0e-6);
	testProcedure(taylorFlat::gamma,linearization::gamma,
		domain(4,4,4,6.3001,4,4), domain(6.3001,6.3001,6.3001,8,6.3001,6.3001),
		"taylorFlat::gamma",1.0e-5);
	testProcedure(taylorFlat::vor,linearization::vorAnalytic,
		domain(4,4,4,6.3001,4,4), domain(6.3001,6.3001,6.3001,8,6.3001,6.3001),
		"taylorFlat::vor",5.0e-5);
	testProcedure(taylorFlat::vor1385,linearization::Vor1385,
		domain(4,4,4,6.3001,4,4), domain(6.3001,6.3001,6.3001,8,6.3001,6.3001),
		"taylorFlat::vor1385",5.0e-5);

	testProcedure(taylorUpright::dih,linearization::dih,
		domain(6.3001,4,4,4,4,4), domain(8,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorUpright::dih",1.0e-5);
	testProcedure(taylorUpright::dih2,linearization::dih2,
		domain(6.3001,4,4,4,4,4), domain(8,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorUpright::dih2",5.0e-6);
	testProcedure(taylorUpright::dih3,linearization::dih3,
		domain(6.3001,4,4,4,4,4), domain(8,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorUpright::dih3",5.5e-6);
	testProcedure(taylorUpright::sol,linearization::solid,
		domain(6.3001,4,4,4,4,4), domain(8,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorUpright::sol",5.0e-6);
	testProcedure(taylorUpright::gamma,linearization::gamma,
		domain(6.3001,4,4,4,4,4), domain(8,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorUpright::gamma",1.0e-5);
	testProcedure(taylorUpright::vor,linearization::vorAnalytic,
		domain(6.3001,4,4,4,4,4), domain(8,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorUpright::vor",4.0e-5);
	testProcedure(taylorUpright::vorVc,linearization::uprightVorVc,
		domain(6.3001,4,4,4,4,4), domain(8,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorUpright::vorVc",4.0e-5);
	testProcedure(taylorUpright::swapVorVc,linearization::uprightVorVcInverted,
		domain(6.3001,4,4,4,4,4), domain(8,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorUpright::swapVorVc",4.0e-5);
	testProcedure(taylorUpright::swapVor,linearization::VorInverted,
		domain(6.3001,4,4,4,4,4), domain(8,6.3001,6.3001,6.3001,6.3001,6.3001),
		"taylorUpright::swapVor",4.0e-5);

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
	lineInterval c = t.center();
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

	/* test taylorSimplex::highVorVc*/ {
	domain x(6.31,4.1,4.2,4.3,4.4,4.5);
	domain z(6.31,4.1,4.2,4.3,4.4,4.5);
	taylorInterval t = taylorSimplex::highVorVc.evalf(x,z);
	if ((!epsilonClose( t.upperBound(),"-0.05976442469703692",1.0e-8))||
		(!epsilonClose( t.lowerBound(),"-0.05976442469703692",1.0e-8))||
		(t.lowerBound()>t.upperBound()))
		cout << "highVorVc fails1 " << endl;
	double Df[6]={0.0175722303720969,-0.07779847831117185,
			-0.07353976251635879,-0.02658067445289348,
			-0.01639262165267792,-0.01714539200252311};
	for (int i=0;i<6;i++) 
	if (fabs(-Df[i]+t.upperPartial(i))>1.0e-8) 
	 cout << "highVorVc2 fails" << endl;
	}

	/*
	cout << " -- not tested :  " <<
		" \n      taylorInterval::upper/lowerboundQ \n";
	*/

}
