#include "error.h"
#include <float.h>
#include <iomanip.h>
#include <iostream>
#include <sstream>
#include <string.h>
#include "interval.h"
#include "lineInterval.h"
#include "secondDerive.h"
#include "taylorInterval.h"
#include "recurse.h"
#include <time.h>
#include <string.h>
#include <stdlib.h>

using namespace std;

void selfTest()
	{
	interMath::selfTest();
	linearization::selfTest();
	secondDerive::selfTest();
	taylorFunction::selfTest();
	}

int generic(const domain& x,const domain& z,const taylorFunction& F)
    {
	domain x0 = x,z0 = z;
	const taylorFunction* I[1] = {&F};
	cellOption opt;
    return prove::recursiveVerifier(0,x,z,x0,z0,I,1,opt);
    }

int testRun()
	{
	interval tx[6]={"4","4","4","6.3001","4","4"};
	interval tz[6]={"6.3001","6.3001","6.3001","6.3001","6.3001","6.3001"};
	domain x = domain::lowerD(tx);
	domain z = domain::upperD(tz);
	taylorFunction F = taylorSimplex::dih*"-1"+taylorSimplex::unit*"1.153093";
	return generic (x,z,F);
	}

int testRunQ()
{
	interval txA[6]={"4","4","4","6.3001","4","4"};
	interval tzA[6]={"6.3001","6.3001","6.3001","6.3001","6.3001","6.3001"};
	domain xA = domain::lowerD(txA);
	domain zA = domain::upperD(tzA);
	interval txB[6]={"4","4","4","6.3001","4","4"};
	interval tzB[6]={"6.3001","6.3001","6.3001","6.3001","6.3001","6.3001"};
	domain xB = domain::lowerD(txB);
	domain zB = domain::upperD(tzB);
	taylorFunction FA = taylorSimplex::dih*"-1"+taylorSimplex::unit*"1.153093";  // dih > 0.1.
	taylorFunction FB = taylorSimplex::unit * "0";
	const taylorFunction* IA[1] = {&FA};
	const taylorFunction* IB[1] = {&FB};
	cellOption opt;
	return prove::recursiveVerifierQ(0,xA,xB,zA,zB,IA,IB,1,opt);
}

main()
	{
	selfTest();
	cout.precision(20);
	if (testRun()) 
		cout << "YES!"; else cout << "NO!" ;
	if (testRunQ()) 
		cout << "YES Q!"; else cout << "NO Q!" ;
	cout << "\nhello" << endl;


	}
