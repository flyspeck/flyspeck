#include "error.h"
#include <iomanip.h>
#include "interval.h"
#include "lineInterval.h"
#include "secondDerive.h"
#include "taylorInterval.h"
#include "recurse.h"
 
// stuff for truncation....
 
void selfTest()
    {
    interMath::selfTest();
    linearization::selfTest();
    secondDerive::selfTest();
    taylorFunction::selfTest();
    }

taylorFunction tauVc = 
	taylorSimplex::sol*"0.100444571427056395"+taylorSimplex::highVorVc*"-1";

int generic246(const domain& x,const domain& z,const taylorFunction& F)
    {
    domain x0 = x,z0 = z;
    const taylorFunction* I[1] = {&F};
    cellOption opt;
	opt.setDihMax(2.46);
    return prove::recursiveVerifier(0,x,z,x0,z0,I,1,opt);
    }


int VerifyAnchored(interval C,interval Cdih,
	// verify P < C + Cdih dih, where P is determined by type.
	int type/*(type==1?-tauVc:highVorVc)*/)
	{
	domain x,z;
	{
	interval tx[6]={"6.3001","4","4","8","4","4"};
    interval tz[6]={"8","6.3001","6.3001","10.24","6.3001","6.3001"};
    x = domain::lowerD(tx);
    z = domain::upperD(tz);
	}
	taylorFunction P = (type==1?tauVc*"-1":taylorSimplex::highVorVc);
	taylorFunction Q251 = (type==1?adhoc20::tauspecial251*"-1":
							adhoc20::vorspecial251);
	taylorFunction Q2 = (type==1?adhoc20::tauspecial2*"-1":
							adhoc20::vorspecial2);
	taylorFunction F = P +Q251
		+taylorSimplex::unit*(-C)
		+taylorSimplex::dih*(-Cdih);
	F.setReducibleState(0);  // adhocs are not reducible.
	if (type==1)
		{
		/* 
		ineq4.html Note 952096899 justifies skipping type==0 .
		ineq4.html Note 942752615 justifies setting z[4]==9, z[1],z[2]=4.84.
		*/
		interval tz1[6]={"8","4.84","4.84","9","6.3001","6.3001"};
		z1 = domain::upperD(tz1);
		if (!generic246(x,z1,F)) ) return 0;
		}
	taylorFunction G = P + Q2
        +taylorSimplex::unit*(-C)
        +taylorSimplex::dih*(-Cdih);
    G.setReducibleState(0);
	return generic246(x,z,G);
	}

int VerifyAnchoredVor(interval C,interval Cdih,
	{
	domain x,z;
	{
	interval tx[6]={"6.3001","4","4","8","4","4"};
    interval tz[6]={"8","6.3001","6.3001","10.24","6.3001","6.3001"};
    x = domain::lowerD(tx);
    z = domain::upperD(tz);
	}
	taylorFunction P = taylorSimplex::highVorVc;
	taylorFunction Q2 = adhoc20::vorspecial2;
	taylorFunction F = P +Q2
		+taylorSimplex::unit*(-C)
		+taylorSimplex::dih*(-Cdih);
	F.setReducibleState(0);  // adhocs are not reducible.
	return generic246(x,z1,F);
	}

int VerifyUpright(interval C,interval Cdih,
	// verify P < C + Cdih dih, where P is determined by type.
	int type/*(type==1?-tauVc:highVorVc)*/)
	{
	domain x,z;
	{
	interval tx[6]={"6.3001","4","4","4","4","6.3001"};
    interval tz[6]={"8","6.3001","6.3001","6.3001","6.3001","6.3001"};
    x = domain::lowerD(tx);
    z = domain::upperD(tz);
	}
	taylorFunction P = (type==1?tauVc*"-1":taylorSimplex::highVorVc);
	taylorFunction F = P 
		+taylorSimplex::unit*(-C)
		+taylorSimplex::dih*(-Cdih);
	F.setReducibleState(1);  
	if (!prove::generic(x,z,F)) return 0;
	taylorFunction G = P 
        +taylorSimplex::unit*(-C)
        +taylorSimplex::dih*(-Cdih);
    G.setReducibleState(1);
	return prove::generic(x,z,G);
	}

void verify(int identifier) 
	{
	cout << "Begin verification of " << identifier << endl;
	error::printTime();
	int t;
	switch(identifier)
		{

		// Section A22:
		case 53502142: t=VerifyAnchoredVor(
			interval("-3.58"),interval("2.28501"),0);
			break;
		case 134398524: t=VerifyAnchoredVor(
			interval("-2.715"),interval("1.67382"),0);
			break;
		case 371491817: t=VerifyAnchoredVor(
			interval("-1.517"),interval("0.8285"),0);
			break;
		case 832922998: t=VerifyAnchoredVor(
			interval("-0.858"),interval("0.390925"),0);
			break;
		case 724796759: t=VerifyAnchoredVor(
			interval("-0.358")+interval("0.009"),interval("0.12012"),0);
			break;
		case 431940343: t=VerifyAnchoredVor(
			interval("-0.186")+interval("0.009"),interval("0.0501"),0);
			break;
		case 980721294: t=VerifyUpright(
			interval("-3.58")/interval("2"),interval("2.28501"),0);
			break;
		case 989564937: t=VerifyUpright(
			interval("-2.715")/interval("2"),interval("1.67382"),0);
			break;
		case 263355808: t=VerifyUpright(
			interval("-1.517")/interval("2"),interval("0.8285"),0);
			break;
		case 445132132: t=VerifyUpright(
			interval("-0.858")/interval("2"),interval("0.390925"),0);
			break;
		case 806767374: t=VerifyUpright(
			(interval("-0.358")+interval("0.009"))/interval("2")
				+interval("0.2")*interval("-1.23"),
			interval("0.12012")+interval("0.2"),0);
			break;
		case 511038592: t=VerifyUpright(
			(interval("-0.186")+interval("0.009"))/interval("2")
				+interval("0.2")*interval("-1.23"),
			interval("0.0501")+interval("0.2"),0);
			break;

		// Section A23:
		case 666753311:
			error::message("not installed");
			break;
		case 4591018: t=VerifyAnchored(
			interval("-3.48")-interval("0.06585"),interval("2.1747"),1);
			break;
		case 193728878: t=VerifyAnchored(
            interval("-3.06")-interval("0.06585"),interval("1.87427"),1);
            break;
		case 2724096: t=VerifyAnchored(
            interval("-1.58")-interval("0.06585"),interval("0.83046"),1);
            break;
		case 213514168: t=VerifyAnchored(
            interval("-1.06")-interval("0.06585"),interval("0.48263"),1);
            break;
		case 750768322: t=VerifyAnchored(
            interval("-0.83")-interval("0.06585"),interval("0.34833"),1);
            break;
		case 371464244: t=VerifyAnchored(
            interval("-0.50")-interval("0.06585"),interval("0.1694"),1);
            break;
		case 657011065: t=VerifyAnchored(
            interval("-0.29")+interval("0.0014")-interval("0.06585"),
			interval("0.0822"),1);
            break;
		case 953023504: t=VerifyUpright(
			interval("-3.48")/interval("2")-interval("0.06586")/interval("2"),
			interval("2.1747"),1);
			break;
		case 887276655: t=VerifyUpright(
			interval("-3.06")/interval("2")-interval("0.06586")/interval("2"),
			interval("1.87424"),1);
			break;
		case 246315515: t=VerifyUpright(
			interval("-1.58")/interval("2")-interval("0.06586")/interval("2"),
			interval("0.83046"),1);
			break;
		case 784421604: t=VerifyUpright(
			interval("-1.06")/interval("2")-interval("0.06586")/interval("2"),
			interval("0.48263"),1);
			break;
		case 258632246: t=VerifyUpright(
			interval("-0.83")/interval("2")-interval("0.06586")/interval("2"),
			interval("0.34833"),1);
			break;
		case 404164527: t=VerifyUpright(
			interval("-0.50")/interval("2")-interval("0.06586")/interval("2")
			-interval("0.003")*interval("1.23"),
			interval("0.1694")+interval("0.003"),1);
			break;
		case 163088471: t=VerifyUpright(
			interval("-0.29")/interval("2")+interval("0.0014")/interval("2")
			-interval("0.06586")/interval("2")
			-interval("0.2")*interval("1.23"),
			interval("0.0822")+interval("0.2"),1);
			break;
		}

		
		
	
	if (t) cout << "Verification complete" << endl;
	else cout << "FAIL! " << identifier << endl;
	error::printTime();
	}


main()
	{
	cout << "\n\nVerifications A23" << endl;
	selfTest();
	verify(666753311);
	verify(4591018);
	verify(193728878);
	verify(2724096);
	verify(213514168);
	verify(750768322);
	verify(371464244);
	verify(657011065);
	error::diagnostic();

	cout << "\n\nVerifications A23, part2" << endl;
	selfTest();
	verify(953023504);
	verify(887276655);
	verify(246315515);
	verify(784421604);
	verify(258632246);
	verify(404164527);
	verify(163088471);
	}
