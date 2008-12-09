#include <iomanip.h>
#include "taylorInterval.h"


class basisFunction 
{
public:
	double (*fn)();
	double evalf() { return (*fn)() ; }
	basisFunction (double (*r)()) { fn = r; }
};

class details 
{
public:
    int difforder;
    int reducible;
    basisFunction** basisVector;
    double* basisCoeff;
    int basisCount;
    int basisCapacity;
	details(int capacity) { 
		difforder=reducible=basisCount=basisCapacity=0;
		basisCoeff=0; basisVector=0;
		if (capacity>0) {
			basisCapacity=capacity;
			basisVector= new basisFunction*[basisCapacity];
			basisCoeff= new double[basisCapacity];
			}
		}
	~details() {
		if (basisVector)  delete[] basisVector;
		if (basisCoeff)  delete[] basisCoeff; 
		}
	details(const details& rhs)
		{
		basisVector = new (basisFunction*[rhs.basisCapacity]);
		basisCoeff = new double[rhs.basisCapacity];
		difforder=rhs.difforder;
		reducible=rhs.reducible;
		basisCount = rhs.basisCount;
		basisCapacity=rhs.basisCapacity;
		for (int i=0;i<basisCapacity;i++)
			{
			basisCoeff[i]=rhs.basisCoeff[i];
			basisVector[i]=rhs.basisVector[i];
			}
		}
		
};

taylorFunction::taylorFunction(int c) { X = new details(c); }
taylorFunction::taylorFunction(basisFunction& x)
	{
	X = new details(1);
	X->basisVector[0]= &x;
	X->basisCoeff[0]= 1.0;
	X->basisCount=1;
	X->basisCapacity=1;
	}
int taylorFunction::getOrderOfDifferentiability() { return X->difforder; }
int taylorFunction::getReducibleState() { return X->reducible; }
void taylorFunction::setReducibleState(int r) { X->reducible = r; }

void taylorFunction::scale(taylorFunction& u,double t)
	{
	for (int i=0;i<u.X->basisCount;i++) 
		{
		u.X->basisCoeff[i]= t*u.X->basisCoeff[i];
		u.X->basisVector[i] = u.X->basisVector[i];
		}
	}

const int increment = 1;

void taylorFunction::add(const taylorFunction& f)
	{
    int i,j,match;
    for (i=0;i<f.X->basisCount;i++)
        {
        match=0;
        for (j=0;j<X->basisCount;j++)
            {
            if (match) continue;
            if (X->basisVector[j]==f.X->basisVector[i])
                {
                X->basisCoeff[j]=X->basisCoeff[j]+f.X->basisCoeff[i];
                match=1;
                }
            }
        if (!match)
            {
            if (X->basisCount>=X->basisCapacity) 
				{
				basisFunction**temp = new (basisFunction* 
					[X->basisCapacity+increment]);
				double* stemp = new double[X->basisCapacity+increment];
				//if ((!stemp)||(!temp)) error::message("allocation failed");
				for (int r =0;r<X->basisCapacity;r++)
					{
					temp[r]= X->basisVector[r];
					stemp[r]= X->basisCoeff[r];
					}
				delete[] X->basisVector;
				delete[] X->basisCoeff;
				X->basisVector = temp;
				X->basisCoeff = stemp;
				}
            X->basisVector[X->basisCount]=f.X->basisVector[i];
            X->basisCoeff[X->basisCount]=f.X->basisCoeff[i];
            X->basisCount++;
            }
        }
    }

taylorFunction::~taylorFunction()
	{
	if (X) delete X;
	}


double taylorFunction::evalf()
	{
	double t = 0;
	for (int i=0;i<X->basisCount;i++)
		t += (X->basisVector[i]->evalf())*(X->basisCoeff[i]);
	return t;
	}

static double r7() { return 7.0; }
static double r8() { return 8.0; }
static double r9() { return 9.0; }

class taylorTest 
{
public:
	taylorTest() {
		cout << " -- loading taylor interval routines $Revision$" << endl;
	basisFunction P7(r7);
	cout << P7.evalf() << endl;
	taylorFunction R7(P7);
	cout << R7.evalf() << endl;
	R7.add(R7);
	cout << R7.evalf() << endl;
	basisFunction P8(r8);
	taylorFunction R8(P8);
	R7.add(R8);
	cout << R7.evalf() << endl;
	cout << R8.evalf() << endl;
	taylorFunction::scale(R7,3);
	cout << R7.evalf() << endl;
	
		
	}
};

static taylorTest E;
