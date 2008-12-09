//  copyright (c) 1997, Thomas C. Hales, all rights reserved.

#include <iomanip.h>
#include <iostream.h>
extern "C"
{
#include <math.h>
#include <stdlib.h>
//#include <sys/time.h>
//#include <sys/resource.h>
}
#include "error.h"
#include "interval.h"
#include "taylorInterval.h"
#include "recurse.h"
#include "secondDerive.h"
#include "recurseQ.h"


// Leaner version of part3.cc  


static const interval zp("0.10044457142705639500004992359");

static ineq reduce(&sec_combo,&combo_fn,1);
static ineq irreducible(&sec_combo,&combo_fn,0);

void report(int random) 
	{
	cout << "\nVerification complete of inequality number "
		<< random << endl  << flush;
	}
void report(int random,int i) 
	{
	cout << "\nVerification complete of inequality number "
		<< random << " " << i << endl  << flush;
	}

void set(ineq I[],int i,combo* Aptr)
	{
	I[i].setdetails((int*) Aptr);
	}

interval sq(interval x)
	{
	return x*x;
	}

combo C(interval x)
	{
	return simplex::scalar*x;
	}

int qrtetrahedron(interval X[6],interval Z[6],
	combo& lc,   // gamma term supplied by proc,
	int notreducible=0)
	{
	double x[6],z[6],x0[6],z0[6];
	combo c141 = C(sq("1.41"));
        for (int i=0;i<6;i++) 
		{ x[i]=x0[i]=inf(X[i]); z[i]=z0[i]=sup(Z[i]); }
	// Gamma:
        ineq I[2] = {reduce,reduce};
	if (notreducible) I[0]=irreducible;
	combo A,B,C1,D;
	A = qrtet::gamma+lc;
        set(I,0,&A);
	B = -qrtet::rad2 + c141;
	set(I,1,&B);
	if (!recursive_verifier(0,x,z,x0,z0,I,2)) return 0;
	// Voronoi:
	I[1]=irreducible;
	C1 = qrtet::vor+lc;
	set(I,0,&C1);
	D = qrtet::rad2-c141;
	set(I,1,&D);
        return recursive_verifier(0,x,z,x0,z0,I,2);
	}

void std(interval x[6],interval z[6])
	{
	static const interval s("6.3001");
	for (int i=0;i<6;i++){ x[i]=four; z[i]=s;  }
	}

void quadcluster(interval XA[6],interval XB[6],
		interval ZA[6],interval ZB[6],
	combo& lcA,combo& lcB)
	{
	double xA[6],xB[6],zA[6],zB[6];
        for (int i=0;i<6;i++) 
		{ xA[i]=inf(XA[i]); zA[i]=sup(ZA[i]); 
		  xB[i]=inf(XB[i]); zB[i]=sup(ZB[i]); }
        ineq IA[1] = {reduce}, IB[1]={reduce};
	set(IA,0,&lcA); set(IB,0,&lcB);
	recursive_verifierQ(0,xA,xB,zA,zB,IA,IB,1);
	}

void quadcluster2(interval XA[6],interval XB[6],
		interval ZA[6],interval ZB[6],
	combo& lcA,combo& lcA2,combo& lcB,combo& lcB2)
	{
	double xA[6],xB[6],zA[6],zB[6];
        for (int i=0;i<6;i++) 
		{ xA[i]=inf(XA[i]); zA[i]=sup(ZA[i]); 
		  xB[i]=inf(XB[i]); zB[i]=sup(ZB[i]); }
        ineq IA[2] = {reduce,reduce}, IB[2] = {reduce,reduce};
        set(IA,0,&lcA); set(IA,1,&lcA2);
        set(IB,0,&lcB); set(IB,1,&lcB2);
	recursive_verifierQ(0,xA,xB,zA,zB,IA,IB,2);
	}

int flatquarter(interval X[6],interval Z[6],combo& lc) 
	{ // X[3] is the diagonal.
	double x[6],z[6],x0[6],z0[6];
	int i;
        for (i=0;i<6;i++) { x[i]=x0[i]=inf(X[i]); z[i]=z0[i]=sup(Z[i]); }
        ineq I[3] = {reduce,reduce,reduce};
	combo A = flat::gamma + lc ;
	combo B = -simplex::eta2_456 + simplex::scalar*two;
	combo C1 = -simplex::eta2_234 + simplex::scalar*two;
        set(I,0,&A); set(I,1,&B); set(I,2,&C1);
	if (!recursive_verifier(0,x,z,x0,z0,I,3)) return 0;  
	//Voronoi:
	for (i=1;i<3;i++) I[i]=irreducible;
	A = flat::vor + lc;
	B = -B;
	C1 = -C1;
        set(I,0,&A); set(I,1,&B); set(I,2,&C1);
        return recursive_verifier(0,x,z,x0,z0,I,3);
	}

int flatVc(interval X[6],interval Z[6],combo& lc) 
	{ // X[3] is the diagonal.
	double x[6],z[6],x0[6],z0[6];
        for (int i=0;i<6;i++) { x[i]=x0[i]=inf(X[i]); z[i]=z0[i]=sup(Z[i]); }
	printit(x); printit(z);
        ineq I[1] = {reduce}; 
	combo A = simplex::vorVc + lc ;
	set(I,0,&A);
	return recursive_verifier(0,x,z,x0,z0,I,1);  
	}

int uprightquarter(interval X[6],interval Z[6], 
	combo& lc) 
	{ // xx0[0] is the diagonal.
	int i;
	double x[6],z[6],x0[6],z0[6];
        for (i=0;i<6;i++) { x[i]=x0[i]=inf(X[i]); z[i]=z0[i]=sup(Z[i]); }
	printit(x); printit(z);
        ineq I[3] = {reduce,reduce,reduce};
	combo A = upright::gamma + lc ;
	combo B = -simplex::eta2_126 + simplex::scalar*two;
	combo C1 = -simplex::eta2_135 + simplex::scalar*two;
        set(I,0,&A); set(I,1,&B); set(I,2,&C1);
	if (!recursive_verifier(0,x,z,x0,z0,I,3)) return 0;  
	for (i=1;i<3;i++) I[i]=irreducible;
	A = upright::vor + lc;
	B = -B;
	C1 = -C1;
        set(I,0,&A); set(I,1,&B); set(I,2,&C1);
        return recursive_verifier(0,x,z,x0,z0,I,3);
	}

// same but averaged on upright.
int uprightquarterAV(interval X[6],interval Z[6], 
	combo& lc) 
	{ // X[0] is the diagonal.
	int i;
	double x[6],z[6],x0[6],z0[6];
        for (i=0;i<6;i++) { x[i]=x0[i]=inf(X[i]); z[i]=z0[i]=sup(Z[i]); }
        ineq I[3] = {reduce,reduce,reduce};
	combo A = upright::gamma + lc ;
	combo B = -simplex::eta2_126 + simplex::scalar*two;
	combo C1 = -simplex::eta2_135 + simplex::scalar*two;
        set(I,0,&A); set(I,1,&B); set(I,2,&C1);
	if (!recursive_verifier(0,x,z,x0,z0,I,3)) return 0;
	for (i=1;i<3;i++) I[i]=irreducible;
	A = (upright::vor+upright::swap_vor)*(one/two) + lc;
	B = -B;
	C1 = -C1;
        set(I,0,&A); set(I,1,&B); set(I,2,&C1);
        return recursive_verifier(0,x,z,x0,z0,I,3);
	}

// same but averaged on upright.// no eta constraint 
int uprightquarterAV_keineta(interval X[6],interval Z[6], 
	combo& lc) 
	{ // X[0] is the diagonal.
	int i;
	double x[6],z[6],x0[6],z0[6];
        for (i=0;i<6;i++) { x[i]=x0[i]=inf(X[i]); z[i]=z0[i]=sup(Z[i]); }
        ineq I[1] = {reduce};
	combo A = upright::gamma + lc ;
        set(I,0,&A);
	if (!recursive_verifier(0,x,z,x0,z0,I,1)) return 0;
	I[0]=irreducible;
	A = (upright::vor+upright::swap_vor)*(one/two) + lc;
	set(I,0,&A);
        return recursive_verifier(0,x,z,x0,z0,I,1);
	}

int generic(interval X[6],interval Z[6],combo& lc) 
	{
	double x[6],z[6],x0[6],z0[6];
        for (int i=0;i<6;i++) { x[i]=x0[i]=inf(X[i]); z[i]=z0[i]=sup(Z[i]); }
        ineq I[1] = {irreducible};
        set(I,0,&lc);
	return recursive_verifier(0,x,z,x0,z0,I,1);  
	}

int generic_reduce(interval X[6],interval Z[6],combo& lc) 
	{
	double x[6],z[6],x0[6],z0[6];
        for (int i=0;i<6;i++) { x[i]=x0[i]=inf(X[i]); z[i]=z0[i]=sup(Z[i]); }
        ineq I[1] = {reduce};
        set(I,0,&lc);
	return recursive_verifier(0,x,z,x0,z0,I,1);  
	}

//******************************* NOW FOR PARTICULAR CASES ***************

void ineq569211440() // BUGGED Needs rerunning.
	{
	// Case CC[6], Prop 4.1, Part III, truncation(t=sq).
	interval b("0.41717"); interval a("0.3");
	interval xA[6],xB[6],zA[6],zB[6];
	std(xA,zA); std(xB,zB);
	xA[3]=xB[3]= eight; zA[3]=zB[3]= interval("12.6002");
	combo A = simplex::vorSqc + simplex::sol*a;
	combo B = A - simplex::scalar*b;
	cout << "ineq569211440" << a << b << endl;
	static const int N=10; int skiplist[N]={3,5,7,8,9,10,12,14,15,16};
	skipcases(skiplist,N);
	quadcluster(xA,xB,zA,zB,A,B);
	}

void ineq884882165()
	{
	// Case CC[10], Prop 4.1.14, Part III, truncation(t=sq). R0
	interval b("-0.1317"); interval a= -zp;
	interval xA[6],xB[6],zA[6],zB[6];
	std(xA,zA); std(xB,zB);
	xA[3]=xB[3]= eight; zA[3]=zB[3]= interval("12.6002");
	combo A = simplex::vorSqc + simplex::sol*a;
	combo B = A - simplex::scalar*b;
	cout << "ineq884882165" << a << b << endl;
	static const int N=17; 
	int skiplist[N]={1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17};
	skipcases(skiplist,N);
	quadcluster(xA,xB,zA,zB,A,B);
	report(884882165);
	}

int ineq48086475()
	{
	// Case CC[6], Prop 4.1, Part III, truncation(t=vc,104).
	static const interval pt("0.05537364566846386973007384184");
	interval b("0.41717"); interval a("0.3");
	interval xA[6],xB[6],zA[6],zB[6];
	std(xA,zA); std(xB,zB);
	xA[3]=xB[3]= eight; zA[3]=zB[3]= interval("12.6002");
	combo A = simplex::vorVc + simplex::sol*a;
	combo B = A - simplex::scalar*b;
	combo A1= simplex::sol*a;
	combo B1= A1 + simplex::scalar*(-b + interval("-1.04")*pt);
	cout << "ineq48086475" << a << b << endl;
	static const int N=10; int skiplist[N]={3,5,7,8,9,10,12,14,15,16};
	skipcases(skiplist,N);
	quadcluster2(xA,xB,zA,zB,A,A1,B,B1);
	return 1;
	}

void ineq637597013()
	{
	// Case CC[10], Prop 4.1, Part III, truncation(t=vc,104).
	static const interval pt("0.05537364566846386973007384184");
	interval b("-0.1317"); interval a= -zp;
	interval xA[6],xB[6],zA[6],zB[6];
	std(xA,zA); std(xB,zB);
	xA[3]=xB[3]= eight; zA[3]=zB[3]= interval("12.6002");
	combo A = simplex::vorVc + simplex::sol*a;
	combo B = A - simplex::scalar*b;
	combo A1= simplex::sol*a;
	combo B1= A1 + simplex::scalar*(-b + interval("-1.04")*pt);
	cout << "ineq637597013" << a << b << endl;
	static const int N=10; int skiplist[N]={3,5,7,8,9,10,12,14,15,16};
	skipcases(skiplist,N);
	quadcluster2(xA,xB,zA,zB,A,A1,B,B1);
	}

void ineq159722518()
	{
	// Case CC[10], Prop 4.1, Part III, truncation(t=vc,104).
	static const interval pt("0.05537364566846386973007384184");
	interval b("-1.0472"); interval a("0.27605");
	interval xA[6],xB[6],zA[6],zB[6];
	std(xA,zA); std(xB,zB);
	xA[3]=xB[3]= eight; zA[3]=zB[3]= interval("12.6002");
	combo A = simplex::vorVc - (simplex::dih+simplex::dih2)*a;
	combo B = simplex::vorVc - simplex::dih2*a - simplex::scalar*b;
	combo A1= - (simplex::dih+simplex::dih2)*a;
	combo B1= -simplex::dih2*a+simplex::scalar*(-b + interval("-1.04")*pt);
	cout << "ineq159722518" << a << b << endl;
	static const int N=17; 
	int skiplist[N]={1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17};
	skipcases(skiplist,N);
	quadcluster2(xA,xB,zA,zB,A,A1,B,B1);
	}



void ineq15135769() // III.qrtet ineq that didn't go through in 1996.
	{
	interval x[6],z[6];
	std(x,z);   x[0]=sq("2.35");
	combo A = qrtet::dih*"-0.48" + C("0.614");
	if (qrtetrahedron(x,z,A))
		{ report(15135769); }
	}

int ineq766216205() // III qr tet edge length constraints.
	{
	interval x[6],z[6];
	std(x,z);
	combo y456 = simplex::y4+simplex::y5+simplex::y6- C(six);
	combo y123 = simplex::y1+simplex::y2+simplex::y3- C(six);
	combo A = C("0.551285") 
		   + y456*"0.199235" + y123*"-0.377076" - qrtet::sol;
	if (!generic(x,z,A)) return 0;
	report(61170556);
 
	A = C("-0.551286") - y456*"0.320937" + y123*"0.152679" + qrtet::sol;
	if (!generic(x,z,A)) return 0;
	report(713734191);
 
	combo y2356 = simplex::y2+simplex::y3+simplex::y5+simplex::y6-C(eight);
	A = C("1.23095") - y2356*"0.359894"
		+(simplex::y1-C(two))*"0.003" +(simplex::y4-C(two))*"0.685"
		- qrtet::dih;
	if (!generic(x,z,A)) return 0;
	report(14901493);
 
	A = -C("1.23096")+ y2356*interval("0.153598")
		-(simplex::y1-C(two))*interval("0.498")
		-(simplex::y4-C(two))*interval("0.76446")
		+qrtet::dih;
	if (!generic(x,z,A)) return 0;
	report(840903362);
 
	A = -C("0.0553737") +(y123+y456)*interval("0.10857");
	int noreduce=1;
	if (!qrtetrahedron(x,z,A,noreduce)) return 0;
	report(443596305);
	
	A = qrtet::sol*interval("0.419351")
		-C("0.286615") +y123*interval("0.2");
	if (!qrtetrahedron(x,z,A,noreduce)) return 0;
	report(379482324);
	/* This part didn't terminate last session, restart:
	A = -qrtet::sol*zp -C("1.0e-6")
		+y456*interval("0.129119") +y123*interval("0.0845696");
	if (!qrtetrahedron(x,z,A,noreduce)) return 0;
	report(635891520);
	*/
	return 1;
	}

int ineq635891520() //  III qr tet edge length constraints.
	{
	interval x[6],z[6];
	std(x,z);
	combo y456 = simplex::y4+simplex::y5+simplex::y6- C(six);
	combo y123 = simplex::y1+simplex::y2+simplex::y3- C(six);
	combo A = -qrtet::sol*zp -C("1.0e-6")
		+y456*interval("0.129119") +y123*interval("0.0845696");
	int noreduce=1;
	if (!qrtetrahedron(x,z,A,noreduce)) return 0;
	report(635891520);
	return 1;
	}

int ineq527450748() // III. group 11. inequalities tau >0.55 pt, etc.
	{
	cout << "527450748 ";
	combo s = qrtet::sol, d1= qrtet::dih, d2= qrtet::dih2, d3= qrtet::dih3;
	static interval xi= sq("2.1773");
	static const interval pt("0.05537364566846386973007384184");
	interval x[6],z[6];
	combo c55 = C("0.55")*pt;
 
	std(x,z);   x[3]= xi; // 11.1.1;
	combo A = -zp*s + c55;
	if (!qrtetrahedron(x,z,A)) return 0; report(382137463); 
	
	std(x,z); x[3]=x[4]=xi; // 11.1.2;
	A = -zp*s + c55*two;
	if (!qrtetrahedron(x,z,A)) return 0; report(149866062);
 
	std(x,z); z[3]=xi; // 11.1.3;
	A = -zp*s + C("-0.29349") + d1*"0.2384";
	if (!qrtetrahedron(x,z,A)) return 0; report(157341407);
 
	std(x,z); z[3]=z[5]=xi; x[4]=xi; // 11.1.4;
	A = -zp*s + C("-0.26303") + d1*"0.2384";
	if (!qrtetrahedron(x,z,A)) return 0; report(364735366);
 
	std(x,z); z[3]=z[4]=xi; x[5]=xi; // 11.1.5;
	A = -zp*s + C("-0.5565") + (d1+d2)*"0.2384";
	if (!qrtetrahedron(x,z,A)) return 0; report(96377444);
 
	std(x,z); z[3]=z[4]=z[5]=xi;  // 11.1.6;
	A = -zp*s + C("-0.29349")*two + (d1+d2)*"0.2384";
	if (!qrtetrahedron(x,z,A)) return 0; report(533010374);
 
	std(x,z); z[3]=z[4]=z[5]=xi;  // 11.1.7;
	A = -zp*s + C("-0.29349")*three + (d1+d2+d3)*"0.2384";
	if (!qrtetrahedron(x,z,A)) return 0; report(21701718);
	return 1;
	}


int ineq781594394() // III. group 11. inequalities sigma <0.52 pt, etc.
	{
	printtime("781594394");
	combo d1= qrtet::dih, d2= qrtet::dih2, d3= qrtet::dih3;
	static interval xi= sq("2.177303");
	static const interval pt("0.05537364566846386973007384184");
	interval x[6],z[6];
	combo c48 = C("0.48")*pt;
 
	std(x,z);   x[3]= xi; // 11.1.8;
	combo A =  c48-C(pt);
	if (!qrtetrahedron(x,z,A)) return 0; report(416435673); 
	
	std(x,z); x[3]=x[4]=xi; // 11.1.9;
	A = two*c48-C(pt);
	if (!qrtetrahedron(x,z,A)) return 0; report(284387959);
 
	std(x,z); z[3]=xi; // 11.1.10;
	A = C("-0.31023815") + d1*"0.207045";
	if (!qrtetrahedron(x,z,A)) return 0; report(127189420);
 
	std(x,z); z[3]=z[5]=xi; x[4]=xi; // 11.1.11;
	A = C("-0.28365") + d1*"0.207045";
	if (!qrtetrahedron(x,z,A)) return 0; report(942055400);
 
	std(x,z); z[3]=z[4]=xi; x[5]=xi; // 11.1.12;
	A = C("-0.53852") + (d1+d2)*"0.207045";
	if (!qrtetrahedron(x,z,A)) return 0; report(838805111);
 
	std(x,z); z[3]=z[4]=z[5]=xi;  // 11.1.13;
	A = C(pt) +two*C("-0.31023815") + (d1+d2)*"0.207045";
	if (!qrtetrahedron(x,z,A)) return 0; report(612939624);
 
	std(x,z); z[3]=z[4]=z[5]=xi;  // 11.1.14;
	A = two*C(pt) +three*C("-0.31023815") + (d1+d2+d3)*"0.207045";
	if (!qrtetrahedron(x,z,A)) return 0; report(280737646);
	return 1;
	}

int CCHASH =  2032330977;// CHANGE IF CC IS CHANGED.// last changed 5/21/97
interval zp32="0.3214226285665804640001597555";
interval solax = "-0.419351";
interval CC[21][3] = {
        // {solid,const,dih}
        {zero,"-5.7906","4.56766"}, // (modified 5/19/97)
        {zero,"-2.0749","1.5094"},
        {zero,"-0.8341","0.5301"},
        {zero,"-0.6284","0.3878"},  //4.1.5
        {zero,"0.4124","-0.1897"},
        {zero,"1.5707","-0.5905"},
        {"-0.3","0.41717",zero}, // 4.1.10 // (modified)
        {zp,"-5.81446","4.49461"},  // 4.1.11 (modified 5/19/97)
        {zp,"-2.955","2.1406"}, // 4.1.12
        {zp,"-0.6438","0.316"},
        {zp,"-0.1317",zero},
        {zp,"0.3825","-0.2365"},
        {zp,"1.071","-0.4747"},
        {zp32,"-5.77942","4.25863"}, // 4.1.17 (modified 5/19/97).
        {zp32,"-4.893","3.5294"},
        {zp32,"-0.4126",zero},
        {zp32,"0.33","-0.316"}, // 4.1.20
        {solax,"-5.350181","4.611391"},
        {solax,"-1.66174","1.582508"}, // 4.1.22
        {solax,"0.0895","0.342747"}, //4.1.23 (modified 5/21/97)
        {solax,"3.36909","-0.974137"}  // 4.1.26
        };

interval DD[4][2] = {
        // {const,dih} *)
        {"-9.494","3.0508"},
        {"-1.0472","0.27605"}, // changed 5/24/97
        {"0.7602884","-0.198867"},
        {"3.5926","-0.844"}
        };

int drandom[4][2]={{343371114,720157360},
		   {35010575,205845522},
		   {418023373,331596772},
		   {168356420,879077684}}; 

int ineqVSq41(int k) 
	{
	combo Sqc = simplex::vorSqc;
	combo Vc  = simplex::vorVc;
	combo sol = simplex::sol;
	combo d = simplex::dih;
	combo d2 = simplex::dih2;
	static const combo m104pt=C("-0.05758859149520242451927679551");
	interval xA[6],zA[6],xB[6],zB[6];
	std(xA,zA);
	xA[3]=interval("8.0"); zA[3]=interval("12.6002");
	for (int i=0;i<6;i++) { xB[i]=xA[i]; zB[i]=zA[i]; }

	// asym:
	combo A = Sqc-sol*CC[k][0]- C(CC[k][1]) - d*CC[k][2];
	combo B = Sqc-sol*CC[k][0];
	quadcluster(xA,xB,zA,zB,A,B);
	report(593360266,k);
	// side:
	A = Sqc-sol*CC[k][0]- C(CC[k][1]/two) - d2*CC[k][2];
	B = A;
	quadcluster(xA,xB,zA,zB,A,B);
	report(165114342,k);
 
	// asym, -1.04 case:
	combo A2,B2;
	A = Vc      -sol*CC[k][0]- C(CC[k][1]) - d*CC[k][2];
	A2 = m104pt -sol*CC[k][0]- C(CC[k][1]) - d*CC[k][2];
	B = Vc -sol*CC[k][0];
	B2 =   -sol*CC[k][0];
	quadcluster2(xA,xB,zA,zB,A,A2,B,B2);
	report(413555825,k);

	// side:
	A = Vc               -sol*CC[k][0]- C(CC[k][1]/two) - d2*CC[k][2];
	A2= m104pt*(one/two) -sol*CC[k][0]- C(CC[k][1]/two) - d2*CC[k][2];
	B =  A;
	B2 = A2;
	quadcluster2(xA,xB,zA,zB,A,A2,B,B2);
	report(983988054,k);
	return 1;
	}

void ineqVSq42(int k) 
	{
	static const combo Sqc = simplex::vorSqc;
	static const combo Vc =  simplex::vorVc;
	static const combo d = simplex::dih;
	static const combo d2= simplex::dih2;
	static const interval m104pt("-0.05758859149520242451927679551");
	interval s63("6.3001");
	interval xA[6],zA[6],xB[6],zB[6];
	int i;
	for (i=0;i<6;i++){ xA[i]=four;zA[i]=s63;  }
	xA[3]=interval("8.0"); zA[3]=interval("12.6002");
	for (i=0;i<6;i++) { xB[i]=xA[i]; zB[i]=zA[i]; }
	// sq:
	combo A = Sqc - C(DD[k][0]) - d*DD[k][1] - d2*DD[k][1];
	combo B = Sqc-  d2*DD[k][1];
	cout << "BUG: skipping 718728086\n";
	//quadcluster(xA,xB,zA,zB,A,B);
	//report(718728086,k);

	// 104;
	A = Vc - C(DD[k][0]) - d*DD[k][1] - d2*DD[k][1];
        B = Vc-  d2*DD[k][1];
	combo A2,B2;
	A2 = C(m104pt) - C(DD[k][0]) - d*DD[k][1] - d2*DD[k][1];
	B2 = -d2*DD[k][1];
	quadcluster2(xA,xB,zA,zB,A,A2,B,B2);
	report(457860257,k);
	}

void III41VSq()
	{
	static const int N=16;
	int skiplist[N]=
		{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16};
	skipcases(skiplist,N);
	ineqVSq41(6);
	}

void III42VSq()
	{
	static const int N = 16;
	int skiplist[N]=
		{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16};
	skipcases(skiplist,N);
        ineqVSq42(2);
	}

void III42VSqX()
	{ // part3  Prop 4.2.3 (Vc,104) and (VSq) cases all but R0 and R7.
	static const int N = 2;
	int skiplist[N]= {0,7};
	skipcases(skiplist,N);
        ineqVSq42(2);
	}

void Temp42VSqX()
	{ //test case.
	static const int N = 3;
	int skiplist[N]= {0,1,7};
	skipcases(skiplist,N);
	setWCUTOFF(0.1);
        ineqVSq42(2);
	}

#include "part4.inc"

int main()
	{
	printtime();
	//Temp42VSqX();
	//III42VSqX();
	if (!ineq852763473()) { cout << "Failed inequality"; }
	//IV_221b();
	cout << "\n\nALL DONE" << endl << flush;
	printtime();
	return 1;
	}
