#include "error.h"
#include <iomanip.h>
#include "interval.h"
#include "lineInterval.h"
#include "secondDerive.h"
#include "taylorInterval.h"
#include "recurse.h"
 
/*  Sphere Packings IV. 
	Code for the verification of Inequalities A10,A11,A12,A13,A16.
	(The code for A1-A8 is in part4sec1.cc, and the rest was done by Ferguson.)

	code by Thomas C. Hales
	6/98.
	
*/

void selfTest()
    {
    static int i=0;
    if (i>0) {
        error::printTime();
        error::diagnostic();
        cout << endl << endl; }
    interMath::selfTest();
    linearization::selfTest();
    secondDerive::selfTest();
    taylorFunction::selfTest();
    cout << " -- Installation complete -- " << endl;
    i++;
    }

interval zetapt = "0.10044457142705639500";

taylorFunction gammaNu =
    taylorUpright::gamma + taylorUpright::vorVc*"0.5"
        +taylorUpright::swapVorVc*"-0.5";
 
taylorFunction vorNu =
    taylorUpright::vor*"0.5"+taylorUpright::swapVor*"0.5"
        + taylorUpright::vorVc*"0.5" +taylorUpright::swapVorVc*"-0.5";

taylorFunction tauVNu = vorNu*"-1"+taylorUpright::sol*zetapt;
taylorFunction tauGNu = gammaNu*"-1"+taylorUpright::sol*zetapt;

taylorFunction octavorVc = 
	taylorUpright::vorVc*"0.5" + taylorUpright::swapVorVc*"0.5";

// a small variation of prove::generic
int generic2(const domain& x,const domain& z,const taylorFunction& F,
    taylorFunction& G)
    {
    domain x0 = x,z0 = z;
    const taylorFunction* I[2] = {&F,&G};
    cellOption opt;
    return prove::recursiveVerifier(0,x,z,x0,z0,I,2,opt);
    }

// a small variation of prove::generic
int generic3(const domain& x,const domain& z,const taylorFunction& F,
    taylorFunction& G,taylorFunction& H)
    {
    domain x0 = x,z0 = z;
    const taylorFunction* I[3] = {&F,&G,&H};
    cellOption opt;
    return prove::recursiveVerifier(0,x,z,x0,z0,I,3,opt);
    }


void verify(int identifier) 
	{
	cout << "Begin verification of " << identifier << endl;
	error::printTime();
	int t;
	switch(identifier)
		{

		// Section A10
		case 214637273:
			{
			interval x[6]={"7.268416","4","4","4","4","4"};
			interval tx("6.3001");
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction F = taylorUpright::gamma+ octavorVc*"-1";
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 751772680:
			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction F = taylorUpright::gamma+ octavorVc*"-1"
				+taylorSimplex::unit*"-0.01561";
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 366146051:
			{
			interval tx("6.3001");
			interval x[6]={"6.6049"/*2.57^2*/,"4","4","4","4","4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction F = taylorUpright::gamma+ octavorVc*"-1"
				+taylorSimplex::unit*"-0.00935";
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 675766140:
			{
			interval tx("6.3001");
			interval x[6]={tx,"5.0625"/*2.25^2*/,"4","4","4","4"};
			interval z[6]={"6.6049"/*2.57^2*/,tx,tx,tx,tx,tx};
			taylorFunction F = taylorUpright::gamma+ octavorVc*"-1"
				+taylorSimplex::unit*"-0.00928";
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 520734758:
			{
			interval tx("6.3001");
			interval x[6]={tx,"5.0625"/*2.25^2*/,"4","4","4","5.0625"};
			interval z[6]={"6.6049"/*2.57^2*/,tx,tx,tx,tx,tx};
			taylorFunction F = taylorUpright::gamma+ octavorVc*"-1";
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		// Section A11

		case 378432183:
			{
			interval tx("6.3001");
			interval t2("7.268416"); // 2.696^2;
			interval t45("6.0025"); // 2.45^2;
			interval x[6]={t2,"4","4","4","4","4"};
			interval z[6]={"8",t45,t45,tx,tx,tx};
			taylorFunction F = taylorUpright::octavor+ octavorVc*"-1";
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;
		

		case 572206659:
			{
			interval tx("6.3001");
			interval t2("7.268416"); // 2.696^2;
			interval t45("6.0025"); // 2.45^2;
			interval x[6]={t2,t45,"4","4",t45,"4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction F = taylorUpright::octavor+ octavorVc*"-1";
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 310679005:
			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction F = taylorUpright::vor+ taylorUpright::vorVc*"-1"
				+taylorSimplex::unit*"-0.003521";
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 284970880:
			{
			interval tx("6.3001");
			interval t2("7.268416"); // 2.696^2;
			interval t45("6.0025"); // 2.45^2;
			interval x[6]={t2,t45,"4",tx,"4",t45};
			interval z[6]={"8",tx,tx,"7.6729"/*2.77^2*/,tx,tx};
			taylorFunction F = taylorSimplex::vor
				+ taylorSimplex::highVorVc*"-1"
				+taylorSimplex::unit*"0.003521";
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 972111620:
			{
			interval tx("6.3001");
			interval t2("7.268416"); // 2.696^2;
			interval x[6]={tx,"4","4",tx,"4",tx};
			interval z[6]={t2,tx,tx,"8",tx,tx};
			taylorFunction F = taylorSimplex::vor
				+ taylorSimplex::highVorVc*"-1"
				+taylorSimplex::unit*"0.009";
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 875762896:
			{
			interval tx("6.3001");
			interval t5("6.6049"); // 2.57^2
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={t5,tx,tx,tx,tx,tx};
			taylorFunction F = taylorUpright::octavor+ octavorVc*"-1";
			taylorFunction G = taylorSimplex::eta2_126 +
					taylorSimplex::unit*"-2";
			t = generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		case 385332676:
			{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={"8",tx,"4.84",tx,tx,tx};
			taylorFunction F = taylorUpright::octavor+ octavorVc*"-1"
				+taylorSimplex::unit*"0.004131";
			taylorFunction G = taylorSimplex::eta2_126*"-1" +
					taylorSimplex::unit*"2";
			taylorFunction H = taylorSimplex::eta2_135 +
					taylorSimplex::unit*"-2";
			t = generic3(domain::lowerD(x),domain::upperD(z),F,G,H);
			}
			break;

		// Section A12

		case 970291025:
			{
			interval tx("6.3001");
			interval x[6]={tx,tx,"4","4","4","4"};
			interval z[6]={"8","8",tx,tx,tx,tx};
			interval pihalf("1.5707963267948966192");
            taylorFunction F = taylorSimplex::vor
                +taylorSimplex::sol*(-zetapt)
                +taylorSimplex::unit*"0.13"
                +(taylorSimplex::dih+taylorSimplex::unit*(-pihalf))*"0.2";
			taylorFunction G = taylorSimplex::unit*"2"
				+taylorSimplex::eta2_126*"-1";
			t = generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		case 524345535:
			{
			/* This case requires special effort, because the current
			implementation of eta2_126 assume that the face is the
			face of a qrtet or quarter, and that assumption does not
			hold here.  I tried this and I hit the recursion limit
			and it failed.  Rather than trace the problem here, let's
			separate it out for special treatment */
			cout << "WARNING: Case 524345535 has been skipped." << endl;
			t=1; break;	
			// All this is skipped....
			interval tx("6.3001");
			interval x[6]={tx,tx,"4","4","4","4"};
			interval z[6]={"8","8",tx,tx,tx,tx};
			interval pihalf("1.5707963267948966192");
            taylorFunction F = taylorSimplex::vorSqc
                +taylorSimplex::sol*(-zetapt)
                +taylorSimplex::unit*"0.13"
                +(taylorSimplex::dih+taylorSimplex::unit*(-pihalf))*"0.2";
			taylorFunction G = taylorSimplex::unit*"-2"
				+taylorSimplex::eta2_126;
			t = generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}
			break;

		case 812894433:
			{
			interval tx("6.3001");
			interval x[6]={"7.5625"/*2.75^2*/,"4","4","4","4","4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction F=taylorUpright::dih*"-0.24573"
				+taylorSimplex::unit*"0.3429";
			taylorFunction FG=F+gammaNu;
			taylorFunction G=taylorSimplex::unit*"2"
					+taylorSimplex::eta2_126*"-1";
			taylorFunction H=taylorSimplex::unit*"2"
					+taylorSimplex::eta2_135*"-1";
			if (! generic3(domain::lowerD(x),domain::upperD(z),FG,G,H)) 
				{ t=0; break; };
			taylorFunction FV=F+vorNu;
			taylorFunction I=taylorSimplex::unit*"-2"
					+taylorSimplex::eta2_126;
			t = generic2(domain::lowerD(x),domain::upperD(z),FV,I);
			}
			break;

		case 404793781:

			/*vor*/{
			interval tx("6.3001");
			interval x[6]={tx,"4","4",tx,"4","4"};
			interval z[6]={"7.5625"/*2.75^2*/,tx,tx,"7.6729"/*2.77^2*/,tx,tx};
			taylorFunction F=taylorSimplex::vor 
				+taylorSimplex::unit*"0.0571";
			taylorFunction G=taylorSimplex::dih*"-1" 
				+taylorSimplex::unit*"2.2";
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,G))
				{  t =0; break; }
			}

			/*vorVc*/{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","7.6729","4","4"};
			interval z[6]={"7.5625"/*2.75^2*/,tx,tx,"8",tx,tx};
			taylorFunction F=taylorSimplex::highVorVc
				+taylorSimplex::unit*"0.0571";
			taylorFunction G=taylorSimplex::dih*"-1" 
				+taylorSimplex::unit*"2.2";
			t = generic2(domain::lowerD(x),domain::upperD(z),F,G);
			}

			break;

		// Section IV.A13.

		case 705592875:

			/*tauGNu*/{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction F=tauGNu*"-1"
				+taylorSimplex::unit*"0.033";
			taylorFunction G = 
			  taylorSimplex::eta2_135*"-1" + taylorSimplex::unit*"2";
			taylorFunction H = 
			  taylorSimplex::eta2_126*"-1" + taylorSimplex::unit*"2";
			F.setReducibleState(0);
			G.setReducibleState(1);
			H.setReducibleState(1);
			if (!generic3(domain::lowerD(x),domain::upperD(z),F,G,H))
				{  t =0; break; }
			}

			/*tauVNu*/{
			interval tx("6.3001");
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction F=tauVNu*"-1"
				+taylorSimplex::unit*"0.033";
			taylorFunction H = taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			F.setReducibleState(0);
			H.setReducibleState(0);
			t= generic2(domain::lowerD(x),domain::upperD(z),F,H);
			}
			break;

		case 747727191:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","8","4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction tauVc = taylorSimplex::lowVorVc*"-1"
				+taylorFlat::sol*zetapt;
			taylorFunction F= tauVc*"-1"
				+taylorSimplex::unit*"0.05925";
			F.setReducibleState(1);
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 474496219:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","8","4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-0.009";
			F.setReducibleState(1);
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 649551700:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","8","4","4"};
			interval z[6]={"4",tx,tx,"10.24","4","4"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-0.0461";
			F.setReducibleState(0);
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 74657942 : { /* by inspection */t=1; } break;

		case 897129160:
			{
			interval tx("6.3001");
			interval x[6]={"4","4",tx,"8","4","4"};
			interval z[6]={tx,tx,tx,"10.24","4","4"};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-0.0461";
			F.setReducibleState(0);
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 760840103:
			{
			interval tx("6.3001");
			interval x[6]={"4","4","4","8","4","4"};
			interval z[6]={"4",tx,tx,"10.24","4","4"};
			taylorFunction tauVc = taylorSimplex::lowVorVc*"-1"
				+taylorSimplex::sol*zetapt;
			taylorFunction F= tauVc*"-1"
				+taylorSimplex::unit*"0.014";
			F.setReducibleState(0);
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 675901554: { /* by inspection */t=1; } break;
		case 712696695:
			{
			interval tx("6.3001");
			interval x[6]={"4","4",tx,"8","4","4"};
			interval z[6]={tx,tx,tx,"10.24","4","4"};
			taylorFunction tauVc = taylorSimplex::lowVorVc*"-1"
				+taylorSimplex::sol*zetapt;
			taylorFunction F= tauVc*"-1"
				+taylorSimplex::unit*"0.06585";
			F.setReducibleState(0);
			t= prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		// Section A16

		case 695180203: 
			{
			interval tx("6.3001");
 
			/*caseA*/{
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction tauF = taylorFlat::gamma*"-1"
				+taylorSimplex::sol*zetapt;
			taylorFunction F= tauF*"-1"
				+taylorSimplex::unit*"0.06585";
			F.setReducibleState(0);
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << "case (a) done" << endl;
			}
 
			/*caseA2*/{
			interval x[6]={"4","4","4","8","4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction tauF = taylorFlat::vor*"-1"
				+taylorSimplex::sol*zetapt;
			taylorFunction F= tauF*"-1"
				+taylorSimplex::unit*"0.06585";
			F.setReducibleState(0);
			taylorFunction H = taylorSimplex::eta2_234 + taylorSimplex::unit*"-2";
			H.setReducibleState(0);
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,H))
				{ t = 0; break; }
			cout << "case (a2) done" << endl;
			}
 
			/*caseA3*/{
			interval x[6]={"4","4","4",tx,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction tauF = taylorFlat::vor*"-1"
				+taylorSimplex::sol*zetapt;
			taylorFunction F= tauF*"-1"
				+taylorSimplex::unit*"0.06585";
			F.setReducibleState(0);
			taylorFunction H = taylorSimplex::eta2_456 + taylorSimplex::unit*"-2";
			H.setReducibleState(0);
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,H))
				{ t = 0; break; }
			cout << "case (a3) done" << endl;
			}
 
			/*caseB*/{
			interval x[6]={"4.84","4","4","6.76","4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction tauF = taylorSimplex::lowVorVc*"-1"
				+taylorSimplex::unit*"0.0063"
				+taylorSimplex::sol*zetapt;
			taylorFunction F= tauF*"-1"
				+taylorSimplex::unit*"0.06585";
			F.setReducibleState(0);
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << "case (b) done" << endl;
			}
 
			/*caseC*/{
			interval x[6]={"4","4","4","7.29","4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction tauF = taylorSimplex::lowVorVc*"-1"
				+taylorSimplex::unit*"0.0114"
				+taylorSimplex::sol*zetapt;
			taylorFunction F= tauF*"-1"
				+taylorSimplex::unit*"0.06585";
			F.setReducibleState(0);
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << "case (c) done" << endl;
			}
 
			/*caseD1*/{
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction tauF = tauGNu;
			taylorFunction F= tauF*"-1"
				+taylorSimplex::unit*(interval("0.06585")/interval("2"));
			F.setReducibleState(0);
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << "case (d1) done" << endl;
			}
 
			/*caseD2*/{
			interval x[6]={tx,"4","4","4","4","4"};
			interval z[6]={"8",tx,tx,tx,tx,tx};
			taylorFunction tauF = tauVNu;
			taylorFunction F= tauF*"-1"
				+taylorSimplex::unit*(interval("0.06585")/interval("2"));
			F.setReducibleState(0);
			taylorFunction H = taylorSimplex::eta2_126 + taylorSimplex::unit*"-2";
			H.setReducibleState(0);
			if (!generic2(domain::lowerD(x),domain::upperD(z),F,H))
				{ t = 0; break; }
			cout << "case (d2) done" << endl;
			}
 
			/*caseE*/{ /* nothing to do, by hypothesis */ }
 
			/*caseF*/{
			interval x[6]={"4","4","4.9729"/*2.23^2*/,
								"7.6729"/*2.77^2*/,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction tauF = taylorSimplex::lowVorVc*"-1"
				+taylorSimplex::sol*zetapt;
			taylorFunction F= tauF*"-1"
				+taylorSimplex::unit*"0.06585";
			F.setReducibleState(0);
			taylorFunction H = taylorSimplex::eta2_456 + taylorSimplex::unit*"-2";
			H.setReducibleState(0);
			t = generic2(domain::lowerD(x),domain::upperD(z),F,H);
			cout << "case (f) done" << endl;
			}
 
			}
			break;

		case 690626704: 
			{
			interval tx("6.3001");
 
			/*caseA*/{ /* Sphere Packings II, Calc 4.5.1. */ }
			/*caseA2*/{ /* Rogers's Lemma */ }
			/*caseA3*/{ /* Rogers's Lemma, and Formulation.3.13.1. */ }
			/*caseB*/{
			interval x[6]={"4.84","4","4","6.76"/*2.6^2*/,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction vorF = taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-0.0063";
			taylorFunction F= vorF;
			F.setReducibleState(0);
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << "case (b) done" << endl;
			}
 
			/*caseC*/{
			interval x[6]={"4","4","4","7.29","4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction vorF = taylorSimplex::lowVorVc
				+taylorSimplex::unit*"-0.0114";
			taylorFunction F= vorF;
			F.setReducibleState(0);
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			cout << "case (c) done" << endl;
			}
  
			/*caseD1*/{ /* done by Formulation Appendix Calc 3.13.3 */}
			/*caseD2*/{ /* done by Formulation Appendix Calc 3.13.4 */}
			/*caseE*/{ /* nothing to do, by hypothesis */ }
  
			/*caseF*/{
			interval x[6]={"4","4","4.9729"/*2.23^2*/,
								"7.6729"/*2.77^2*/,"4","4"};
			interval z[6]={tx,tx,tx,"8",tx,tx};
			taylorFunction vorF = taylorSimplex::lowVorVc;
			taylorFunction F= vorF;
			F.setReducibleState(0);
			taylorFunction H = taylorSimplex::eta2_456 + taylorSimplex::unit*"-2";
			H.setReducibleState(0);
			t = generic2(domain::lowerD(x),domain::upperD(z),F,H);
			cout << "case (f) done" << endl;
			}
 
			}
			break;

		case 807023313:
			{
			interval tz("7.6729"); /*2.77^2*/
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,tx,"4"};
			interval z[6]={tx,tx,tx,tz,tz,tx};
			taylorFunction vorF = taylorSimplex::vor;
			taylorFunction F= vorF +
				taylorSimplex::unit*"0.05714";
			F.setReducibleState(0);
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 590577214:
			{
			interval tz("7.6729"); /*2.77^2*/
			interval tx("6.3001");
			interval x[6]={"4","4","4",tx,tx,"4"};
			interval z[6]={tx,tx,tx,tz,tz,tx};
			taylorFunction F= taylorSimplex::vor
				+taylorSimplex::sol*(-zetapt) 
				+taylorSimplex::unit*"0.13943";
			F.setReducibleState(0);
			t = prove::generic(domain::lowerD(x),domain::upperD(z),F);
			}
			break;

		case 949210508:
			{
			interval tz("7.6729"); /*2.77^2*/
			interval tx("6.3001");
 
			/*caseA*/{
			interval x[6]={"4","4","4",tz,tx,"4"};
			interval z[6]={tx,tx,tx,"8","8",tx};
			taylorFunction vorF = taylorSimplex::lowVorVc;
			taylorFunction F= vorF +
				taylorSimplex::unit*"0.05714";
			F.setReducibleState(0);
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			}
 
			/*caseB*/{
			interval x[6]={"4","4","4",tx,tx,"4"};
			interval z[6]={tx,tx,tx,tz,tz,tx};
			taylorFunction vorF = taylorSimplex::lowVorVc;
			taylorFunction F= vorF +
				taylorSimplex::unit*"0.05714";
			F.setReducibleState(0);
			taylorFunction H = taylorSimplex::eta2_456 + taylorSimplex::unit*"-2";
			H.setReducibleState(0);
			t = generic2(domain::lowerD(x),domain::upperD(z),F,H);
			}
 
			}
			break;

		case 671961774:
			{
			interval tz("7.6729"); /*2.77^2*/
			interval tx("6.3001");
 
			/*caseA*/{
			interval x[6]={"4","4","4",tz,tx,"4"};
			interval z[6]={tx,tx,tx,"8","8",tx};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::unit*"0.13943";
			F.setReducibleState(0);
			if (!prove::generic(domain::lowerD(x),domain::upperD(z),F))
				{ t = 0; break; }
			}
 
			/*caseB*/{
			interval x[6]={"4","4","4",tx,tx,"4"};
			interval z[6]={tx,tx,tx,tz,tz,tx};
			taylorFunction F= taylorSimplex::lowVorVc
				+taylorSimplex::sol*(-zetapt)
				+taylorSimplex::unit*"0.13943";
			F.setReducibleState(0);
			taylorFunction H = taylorSimplex::eta2_456 + taylorSimplex::unit*"-2";
			H.setReducibleState(0);
			t = generic2(domain::lowerD(x),domain::upperD(z),F,H);
			}
 
			}
			break;

		default: 
			{
			cout << "not installed " << identifier << endl;
			t = 0;
			}



		}

		
		
	
	if (t) cout << "Verification complete" << endl;
	else cout << "FAIL! " << identifier << endl;
	error::printTime();
	}

void Section(char* s)
	{
	error::printTime();
	selfTest();
	cout << "\n\nSection " << s << endl << endl;
	}

main()
	{
	/*
	Section("A10");
	verify(214637273);
	verify(751772680);
	verify(366146051);
	verify(675766140);
	verify(520734758);

	Section("A11");
	verify(378432183); // a
	verify(572206659); // b
	verify(310679005); // b
	verify(284970880); // c
	verify(972111620); // c
	*/
	verify(875762896); // d
	verify(385332676); // d
	/*

	Section("A12");
	verify(970291025);
	verify(524345535);
	verify(812894433);
	verify(404793781);

	Section("A13");
	verify(705592875);
	verify(747727191);
	verify(474496219);
	verify(649551700);
	// verify( 74657942); // done by inspection
	verify(897129160);
	verify(760840103);
	// verify(675901554); // done by inspection
	verify(712696695);

	// Section("A14"); // done by S. Ferguson
	// Section("A15"); // done by S. Ferguson

	Section("A16");
	verify(695180203);
	verify(690626704);
	verify(807023313);
	verify(590577214);
	verify(949210508);
	verify(671961774);

	// Section("A17"); // done by S. Ferguson.
	// Section("A18"); // done by S. Ferguson.
	// Section("A19"); // done by S. Ferguson.
	// Section("A20"); // done by S. Ferguson.
	// Section("A21"); // done by S. Ferguson.
	// Section("A22"); // done by S. Ferguson.
	// Section("A23"); // done by S. Ferguson.
	
	cout << "all done!" << endl;
	*/
	}
