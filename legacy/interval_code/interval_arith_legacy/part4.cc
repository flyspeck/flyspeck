/* This is a test program that was used for benchmarks.  It
	runs in a few hours.  It does not perform any essential function.

	Sphere Packings IV.
	Thomas C. Hales
	June 1998
*/

#include "error.h"
#include <iomanip.h>
#include "interval.h"
#include "lineInterval.h"
#include "secondDerive.h"
#include "taylorInterval.h"
#include "recurse.h"

void selfTest()
    {
    interMath::selfTest();
    linearization::selfTest();
    secondDerive::selfTest();
    taylorFunction::selfTest();
    }


static void setqr(domain& x,domain& z)
	{
	interval tx[6]={"4","4","4","4","4","4"};
	interval tz[6]={"6.3001","6.3001","6.3001","6.3001","6.3001","6.3001"};
	x = domain::lowerD(tx);
	z = domain::upperD(tz);
	}

static void setD(domain& x,domain& z,interval x1,interval x2,interval x3,
	interval x4,interval x5,interval x6,
	interval z1,interval z2,interval z3,
	interval z4,interval z5,interval z6)
	{
	interval tx[6]={x1,x2,x3,x4,x5,x6};
	interval tz[6]={z1,z2,z3,z4,z5,z6};
	x = domain::lowerD(tx);
	z = domain::upperD(tz);
	}

int C214637273() // Part IV.A.Sec 3.6.1.
	{
	taylorFunction octavorVc = (taylorUpright::swapVorVc+
		taylorUpright::vorVc)*"0.5";
	interval a("2.696");
	a=a*a;
	interval s("6.3001");
	domain x,z;
	setD(x,z,
		a,"4","4","4","4","4",
		"8",s,s,s,s,s);
	taylorFunction F= taylorUpright::gamma +
			octavorVc*"-1";
	F.setReducibleState(0);
	return prove::generic(x,z,F);
	}


main()
	{
	selfTest();
	if (C214637273())
		cout << "C214637273 done"; else cout << "NO!" ;
		cout << endl;

	error::printTime();
	}
