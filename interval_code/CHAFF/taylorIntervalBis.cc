#include <iomanip.h>
#include "interval.h"
#include "taylorInterval.h"


class details 
{
public:
    int reducible;
    primitive** basisVector;
    interval* basisCoeff;
    int basisCount;
    int basisCapacity;
	details(int capacity) { 
		reducible=basisCount=basisCapacity=0;
		basisCoeff=0; basisVector=0;
		if (capacity>0) {
			basisCapacity=capacity;
			basisVector= new primitive*[basisCapacity];
			basisCoeff= new interval[basisCapacity];
			}
		}
	~details() {
		if (basisVector)  delete[] basisVector;
		if (basisCoeff)  delete[] basisCoeff; 
		}
	details(const details& rhs)
		{
		basisVector = new (primitive*[rhs.basisCapacity]);
		basisCoeff = new interval[rhs.basisCapacity];
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
taylorFunction::taylorFunction(primitive& x)
	{
	X = new details(1);
	X->basisVector[0]= &x;
	X->basisCoeff[0]= interConstant::one;
	X->basisCount=1;
	X->basisCapacity=1;
	}
int taylorFunction::getReducibleState() { return X->reducible; }
void taylorFunction::setReducibleState(int r) { X->reducible = r; }

void taylorFunction::scale(taylorFunction& u,interval t)
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
				primitive**temp = new (primitive* 
					[X->basisCapacity+increment]);
				interval* stemp = new interval[X->basisCapacity+increment];
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
	for (i=0;i<6;i++) for (j=0;j<6;j++) 
		DD[i][j]= t1.DD[i][j]*absC;
	lineInterval s;
	s.f = s.f*c;
	for (i=0;i<6;i++) s.Df[i]=s.Df[i]*c;
	taylorInterval t(flag,s,t1.w,DD);
	return t;
	}
