// Test on Feb 16, 2012 to compute scaledVoronoi Phelan-Weaire foam.
// Revise Feb 21, for sectional Voronoi representation.

#include <iomanip.h>
#include <iostream.h>
#include "Minimizer.h"
#include <math.h>
#include "numerical.h"

double myrand();

double findMinimumEQ(int numargs, int nconstr,
	double* xmin, double* xmax, double* x,
        void (*func)(int numargs,int whichFn,double* x,double* ret,void*),
		     void (*cFunc)(int numargs,int which,double* x,double* ret,void*));


// constructor calls optimizer.  No need to place in main loop.
class trialdata {
public:
  trialdata(Minimizer M,char* s) {
    M.coutReport(s);
  };
};

void printv(double* v,int n) {
  cout << "{";
  for (int i =0;i<n;i++) {
    cout << v[i] << (i==n-1 ? "};" : ",");
  }
}

/*******************************
GENERAL VECTOR ROUTINES
*******************************/

double square(double x) {
  return x*x;
}

// 4D vectors
void add4(double x[4],double y[4],double* ret) {
  for (int i=0;i<4;i++) { ret[i] = x[i] + y[i]; }
}

void scale(double s,double x[4],double* ret) {
  for (int i=0;i<4;i++) { ret[i] = x[i] * s; }
}

// 3D vectors

 double det3(double x[3],double y[3],double z[3]) {
   return (-x[2]*y[1]*z[0] + x[1]*y[2]*z[0] + x[2]*y[0]*z[1] 
	   - x[0]*y[2]*z[1] - x[1]*y[0]*z[2] + x[0]*y[1]*z[2]);
 }

double dot3D(double x[3],double y[3]) {
  return x[0]*y[0] + x[1]*y[1] + x[2]*y[2];
}

void sub3(double x[3],double y[3],double* ret) {
  for (int i=0;i<3;i++) { ret[i] = x[i] - y[i]; }
}

double dist2_3D(double x[3],double y[3]) {
  double z[3];
  sub3(x,y,z);
  return dot3D(z,z);
}

int isparallel(double v1[3],double v2[3],double w1[3],double w2[3]) {
  double z1[3],z2[3],s[3];
  double epsilon = 0.01; // answer gets discretized, precision not needed.
  sub3(v1,v2,z1);
  sub3(w1,w2,z2);
  sub3(z1,z2,s);
  // (v1 -v2) - (w1-w2) = 0?
  return (mabs(dot3D(s,s)) < epsilon);
}

int isneg(double v1[3],double v2[3],double w1[3],double w2[3]) {
  return (isparallel(v1,v2,w2,w1));
}



/*******************************
VOLUMES AND SURFACE AREAS
*******************************/

// analytic volume of a single Rogers simplex.
double RvolAn(double x1, double x2, double x3,double x4,double x5, double x6) {
  return (x1 * (x2 + x6 - x1) * chi(x4,x5,x3,x1,x2,x6)/ 
	  (48.0 * U(x1,x2,x6) * sqrt (delta_x (x1,x2,x3,x4,x5,x6))));
}

// analytic surface area of a single Rogers simplex.
double RsurfAn(double x1,double x2,double x3,double x4,double x5, double x6) {
  return (RvolAn(x1,x2,x3,x4,x5,x6) * (6.0/sqrt(x1)));
}

// analytic volume of a single Vor cell within a dual simplex.
double vol6(double x1,double x2,double x3, double x4, double x5,double x6) {
  return (RvolAn(x1,x2,x3,x4,x5,x6) + RvolAn(x1,x3,x2,x4,x6,x5) +
    RvolAn(x2,x3,x1,x5,x6,x4) + RvolAn(x2,x1,x3,x5,x4,x6) +
	  RvolAn(x3,x1,x2,x6,x4,x5) + RvolAn(x3,x2,x1,x6,x5,x4));
}

// analytic surface of a single Vor cell within a dual simplex
double surf6(double x1,double x2,double x3,double x4,double x5,double x6) {
  return (RsurfAn(x1,x2,x3,x4,x5,x6) + RsurfAn(x1,x3,x2,x4,x6,x5) +
    RsurfAn(x2,x3,x1,x5,x6,x4) + RsurfAn(x2,x1,x3,x5,x4,x6) +
	  RsurfAn(x3,x1,x2,x6,x4,x5) + RsurfAn(x3,x2,x1,x6,x5,x4));
}

// converts squared edge lengths to scaled version by rho.
double xp(double x1,double x2,double x6,double rho1,double rho2) {
  return (x1 * rho1 * rho1 + x2*rho2*rho2 - (x1 + x2 - x6) * rho1 * rho2);
}

double getrho(double v[4], double w[4]) {
  // compute rho(v,w).
  double bvw = v[3] - w[3];  // final space dimension stores information on rho.
  double xvw = dist2_3D(v,w); // compute in 3D
  return 1.0 -  bvw / xvw;  // formula from a mathematical calculation.
}

// Analytic volume of the part of a  scaled Voronoi cell, inside a dual simplex
double vol6rho(double x1,double x2,double x3,double x4,double x5,double x6,
	       double rho1,double rho2,double rho3) {
  double x1p = x1 * rho1 * rho1;
  double x2p = x2 * rho2 * rho2;
  double x3p = x3 * rho3 * rho3;
  double x4p = xp(x2,x3,x4,rho2,rho3);
  double x5p = xp(x1,x3,x5,rho1,rho3);
  double x6p = xp(x1,x2,x6,rho1,rho2);
  return vol6(x1p,x2p,x3p,x4p,x5p,x6p);
}

// Analytic external surface of the part of a  scaled Voronoi cell, inside a dual simplex
double surf6rho(double x1,double x2,double x3,double x4,double x5,double x6,
	       double rho1,double rho2,double rho3) {
  double x1p = x1 * rho1 * rho1;
  double x2p = x2 * rho2 * rho2;
  double x3p = x3 * rho3 * rho3;
  double x4p = xp(x2,x3,x4,rho2,rho3);
  double x5p = xp(x1,x3,x5,rho1,rho3);
  double x6p = xp(x1,x2,x6,rho1,rho2);
  return surf6(x1p,x2p,x3p,x4p,x5p,x6p);
}

 double volvector(double w0[4],double w1[4],double w2[4],double w3[4]) {
   double x1 = dist2_3D(w0,w1);
   double x2 = dist2_3D(w0,w2);
   double x3 = dist2_3D(w0,w3);
   double x4 = dist2_3D(w2,w3);
   double x5 = dist2_3D(w1,w3);
   double x6 = dist2_3D(w1,w2);
   double rho1 = getrho(w0,w1);
   double rho2 = getrho(w0,w2);
   double rho3 = getrho(w0,w3);
   return vol6rho(x1,x2,x3,x4,x5,x6,rho1,rho2,rho3);
 }

 double surfvector(double w0[4],double w1[4],double w2[4],double w3[4]) {
   double x1 = dist2_3D(w0,w1);
   double x2 = dist2_3D(w0,w2);
   double x3 = dist2_3D(w0,w3);
   double x4 = dist2_3D(w2,w3);
   double x5 = dist2_3D(w1,w3);
   double x6 = dist2_3D(w1,w2);
   double rho1 = getrho(w0,w1);
   double rho2 = getrho(w0,w2);
   double rho3 = getrho(w0,w3);
   return surf6rho(x1,x2,x3,x4,x5,x6,rho1,rho2,rho3);
 }

 // w0 cell center.
 // w[i] updated positions of other points.
 // rho[i], scaling factors.
 // k[i][0],k[i][1],k[i][2],  positions of triangles of dual polyhedron around w0,
 // n number of triangles. return the total volume,
double volcell(double w0[4],double wr[27*8][4],int k[24][3],int n) {
   double sum = 0;
   for (int i=0;i<n;i++) {
     int j1 = k[i][0], j2 = k[i][1], j3 = k[i][2];
     double t = volvector(w0,wr[j1],wr[j2],wr[j3]);
     sum += t;
   }
   return sum;
 };;

double surfcell(double w0[4],double wr[27*8][4],int k[24][3],int n) {
   double sum = 0;
   for (int i=0;i<n;i++) {
     int j1 = k[i][0], j2 = k[i][1], j3 = k[i][2];
     sum += surfvector(w0,wr[j1],wr[j2],wr[j3]);
   }
   return sum;
 };;



/*******************************
DATA AND INITIALIZATION
*******************************/

 // initial data
// 0.618 ==> volcell0 = 1.127, volcell1 = 0.88
// 0.55 ==> volcell0 = 1.03, volcell1 = 0.92.
// 0.5 ==> volcell0 = 0.9765, volcell1 = 0.9765.


 double a = 0.5; // this guess turned out to hit the optimal value.

// fourth coordinate is c(i): b(i,j) = c(i) - c(j);


double v0[4]={0,0,0,0};
 double v1[4]={1,1,1};
 double v2[4]={1,0,a};
 double v3[4]={1,0,-a};
 double v4[4]={a,1,0};
 double v5[4]={-a,1,0};
 double v6[4]={0,a,1};
 double v7[4]={0,-a,1};

double e0[4]={2,0,0,0};
double e1[4]={0,2,0,0};
double e2[4]={0,0,2,0};




// global dynamic data

double wi[8][4];  // cell centers.
double f[3][4];  // lattice generators.
double ww[27*8][4];  // coordinates of 8 centers, and their lattice translates by -1,0,1 in x,y,z


// COMBINATORIAL DATA.
// init once.  24=max number of dual triangles.
int kk[8][24][3];   // kk[i][j] is a triple of indices of dual triangle face j of cell i. <=> vertex of sc.Vor.
int nn[8]; // nn[i] is number of dual triangles (i.e. scVor vertices) on cell i.  (12 faces=>(nn=20, etc.)).

int nr[8]; // number of nearest nbrs.
int nbr[8][27*8]; // nearest nbrs
 
 void init_wi_f() {
   for (int i =0;i<3;i++) for (int j=0;j<4;j++) {
       f[i][j] = (i==0 ?e0[j] : (i==1 ? e1 [j] : e2[j]));
     }
   for (int i=0;i<8;i++) for (int j=0;j<4;j++) {
       switch (i) {
       case 0 : wi[i][j] = v0[j]; break;
       case 1 : wi[i][j] = v1[j]; break;
       case 2 : wi[i][j] = v2[j]; break;
       case 3 : wi[i][j] = v3[j]; break;
       case 4 : wi[i][j] = v4[j]; break;
       case 5 : wi[i][j] = v5[j]; break;
       case 6 : wi[i][j] = v6[j]; break;
       case 7 : wi[i][j] = v7[j]; break;
       default : cout << "out of bounds " << endl; break;
       }
       //if (i>0) { wi[i][j] += 0.02 * myrand(); } // debug.
 }
 }

 void setww() {
   for (int i=0;i<3;i++) for (int j=0;j<3;j++) for (int k=0;k<3;k++)  for (int u=0;u<8;u++) {
	   double z[4]={0,0,0,0};
	   double s[4];
	   scale(i-1,f[0],s); add4(z,s,z);
	   scale(j-1,f[1],s); add4(z,s,z);
	   scale(k-1,f[2],s); add4(z,s,z);
	   add4(z,wi[u],z);
	   for (int p=0;p<4;p++) {
	     ww[u + 8*(i+3*j +9*k)][p] = z[p];
	   }
	 }
 }


int isnbr(double v[3],double w[3]) {
    double x1 = mabs(v[0]-w[0]), x2 = mabs(v[1]-w[1]), x3 = mabs(v[2]-w[2]);
     return ((x1 < 1.1) && (x2 < 1.1 ) &&(x3 < 1.1) &&(dist2_3D(v,w) > 0.01) &&
	     (dist2_3D(v,w) < 2.1));
}

 void init_cell_combinatorics (int i) {
   int near=0;
   for (int j=0;j<27*8;j++) {
     assert(near < 27*8);
     if (isnbr(wi[i],ww[j])) {
       nbr[i][near] = j; near++;
     }
   }
   nr[i]=near;
   cout << i << " has " << near << " neighbors" << endl;
   int kc = 0;
   for (int j1=0;j1<near;j1++) for (int j2=0;j2<near;j2++) for (int j3=0;j3<near;j3++) {
	 if (isnbr(ww[nbr[i][j1]],ww[nbr[i][j2]]) && isnbr(ww[nbr[i][j2]],ww[nbr[i][j3]]) && 
	     isnbr(ww[nbr[i][j3]],ww[nbr[i][j1]]) &&
	     (j1 < j2) && (j2 < j3)) {
	   kk[i][kc][0]=nbr[i][j1]; kk[i][kc][1]=nbr[i][j2]; kk[i][kc][2]=nbr[i][j3]; kc++;
	 }
       }
   nn[i]=kc;
   cout << i << " has " << kc << " faces " << endl;
 }

double totalsurface() {
  double sum = 0;
  for (int i=0;i<8;i++) {
    sum += surfcell(wi[i],ww,kk[i],nn[i]);
  }
  return sum;
}

double mu() {
  double t = totalsurface()/(8.0 * 2.0);
  return (t*t*t);
}


// DO A TEST:

void testvol6rho() {
  double u0[4], u1[4],u2[4],u3[4];
  for (int p=0;p<4;p++) {
    u0[p] = wi[0][p] + 0.1*myrand();  // compute using first simplex of k.
    u1[p] = ww[kk[0][0][0]][p] + 0.1*myrand();
    u2[p] = ww[kk[0][0][1]][p] + 0.1*myrand();
    u3[p] = ww[kk[0][0][2]][p] + 0.1*myrand();
  }
  {
    u0[3] = 0.0;
    u1[3] = 0.0;
    u2[3] = 0.0;
    u3[3] = 0.0;
  }  
  double t = volvector(u0,u1,u2,u3) + volvector(u1,u0,u2,u3)+volvector(u2,u0,u1,u3)+
    volvector(u3,u0,u1,u2);
  // repartition the simplex and compare the result.
  double u = volvector(u0,u1,u2,u3);
  {
    u0[3]= 0.1 * myrand();
    u1[3]= 0.1 * myrand();
    u2[3]= 0.1 * myrand();
    u3[3]= 0.1 * myrand();
  }
  double t2 = volvector(u0,u1,u2,u3) + volvector(u1,u0,u2,u3)+volvector(u2,u0,u1,u3)+
    volvector(u3,u0,u1,u2);
  cout << "testvol6rho " << t << " = " << t2 << endl;
  cout << "testvol6rho " << u << " != " << volvector(u0,u1,u2,u3) << endl;
}


/*******************************
 REPORTING FUNCTIONS
*******************************/

void printglobal() {
  cout << "printing ww,f,rhof: " << endl;
  for (int i=0;i<8;i++) {
    cout << "double v" << (i) << "[4]= ";
    printv(wi[i],4);
    cout << endl;
    }
  for (int i=0;i<3;i++) {
    cout << "double e" << (i) << "[4]= ";
    printv(f[i],4);
    cout << endl;
  }
}

int nearf(double xm,double x,double xM) {
  return (min (mabs(x-xm) , mabs(x-xM) )< 1.0e-8);
}

int report_near(double* xmin,double* x,double* xmax) {
  int offset=0;
  cout << "boundaries : " << endl;
  for (int i=1;i<7;i++) for (int j=0;j<4;j++) {
      int u = offset+(i-1)+8*j;
      double a = xmin[u], b = x[u], c = xmax[u];
      if (nearf(a,b,c)) { cout << " w:"<< i <<"," <<j; 
	cout << " " << a << " " << b << " " << c << endl; 
    }
    }
  cout << endl;
  offset += 7*4;
  for (int i=0;i<9;i++) {
    int u = offset + i;
    double a = xmin[u], b = x[u], c = xmax[u];
    if (nearf(a,b,c))  { cout << " f:"<< i ;
      cout << " " << a << " " << b << " " << c << endl; 
    }
    }
  cout << endl;
  //offset += 3*3;
  //    for (int i=0;i<54;i++) { 
  //   int u = offset + i;
  //   double a = xmin[u], b = x[u], c = xmax[u];
  //   if (nearf(a,b,c)) { cout << " rh:"<< i; 	cout << " " << a << " " << b << " " << c << endl; }
  //  }
  cout << endl;
}

/*******************************
DEHN INVARIANT
*******************************/

void print_one_reduced_dih(double w0[3],double w1[3],double w2[3]) {
  double y1 = sqrt(dist2_3D(w0,w1));
  double y2 = sqrt(dist2_3D(w0,w2));
  double y6 = sqrt(dist2_3D(w1,w2));
  cout << "dih : " << (pi()/3.0 - arc(y1,y2,y6)) << endl;
}

void print_reduced_dih() {
  for (int i=2;i<3;i++) for (int j=0;j<nn[i];j++) {
      print_one_reduced_dih(wi[i],ww[kk[i][j][0]],ww[kk[i][j][1]]);
      print_one_reduced_dih(wi[i],ww[kk[i][j][1]],ww[kk[i][j][2]]);
      print_one_reduced_dih(wi[i],ww[kk[i][j][0]],ww[kk[i][j][2]]);
    }
}


/*******************************
NONLINEAR OPTIMIZATION HELP FUNCTIONS AND MAIN
*******************************/

void globalize_x(double* x) {
  // wi[0] fixed at origin.
    for (int i=1;i<8;i++) for (int j=0;j<4;j++) {
	wi[i][j] = x[(i-1) + 7*j];
    }
  int offset = 7*4;
  // f lower triangular with det=8.
  f[0][0]= x[offset+0];
  f[1][0]= x[offset+1];
  f[1][1]= x[offset+2];
  f[2][0]= x[offset+3];
  f[2][1]= x[offset+4];
  f[2][2] = x[offset+5];  //8.0 / (f[0][0] * f[1][1] );
  f[0][3] = x[offset+6];
  f[1][3] = x[offset+7];
  f[2][3] = x[offset +8];
  offset += 9;
  setww();
}

void set_x(double* xmin,double* x,double* xmax,double wslack,double fslack) {
    // set ww
  int offset=0;
    for (int i=1;i<8;i++) for (int j=0;j<4;j++) {
	xmin[offset + (i-1) + 7*j] = wi[i][j] - wslack;
	xmax[offset + (i-1) + 7*j] = wi[i][j] + wslack;
	x[offset + (i-1) + 7*j] = wi[i][j] ;
      }
    offset += 7*4;
    // set f
   x[offset+0] = e0[0];
  x[offset+1] = e1[0];
  x[offset+2] = e1[1];
  x[offset+3] = e2[0];
  x[offset+4] = e2[1];
  x[offset+5] = e2[2];
  x[offset+6] = e0[3];
  x[offset+7] = e1[3];
  x[offset +8] = e2[3];
  for (int i=0;i<9;i++) { 
    int u = offset + i;
    double fs = (i>=6 ? 0.0 : fslack); // debug. no global lattice shift.
    xmin[u] = x[u] - fs;
    xmax[u] = x[u] + fs;
  }
    offset += 9;
}


double weightedmu(double* x) {
  globalize_x(x);
  double xf = 0.0; 
  //  xf =  1000.0;
  double m = mu();
  for (int i =0;i<8;i++) {
    double t = 1.0- volcell(wi[i],ww,kk[i],nn[i]);
    m += xf * t*t;
  }
  //double t = det3(f[0],f[1],f[2]) - 8.0; 
  //m+= xf * t * t;
  return m;
}

// this is minimized
void t1(int numargs,int whichFn,double* x,double* ret,void*) {
  *ret =  weightedmu(x);
};

// constraints 8 vol

void cc(int numargs,int whichFn,double* x, double* ret,void*) {
  globalize_x(x);
  if (whichFn <= 8) {
    int i = whichFn - 1;
    *ret = 1.0- volcell(wi[i],ww,kk[i],nn[i]);
  }
  else if (whichFn <= 16) {
    int i = whichFn - 1 - 8;
    *ret = volcell(wi[i],ww,kk[i],nn[i]) - 1.2;
  }
  else {
    cout << "cc out of range ";
    abort();
    //    int i = whichFn - 9;
    //  *ret = triangle_constraint(i);
  }
}


void pseudoseed(int i) {
  for (int j=0;j<i;j++) { myrand(); }
}

int main() {
  // initialization.
  pseudoseed(8);
  init_wi_f();
  setww();
  for (int i=0;i<8;i++) {
    init_cell_combinatorics(i); 
  }
  testvol6rho();

  // initialize xmin,x,xmax:
  int sz = 7*4+9;
  double xmin[sz];
  double xmax[sz];
  double x[sz];
  double wslack = 0.2;
  double fslack = 0.2;
  set_x(xmin,x,xmax,wslack,fslack);

  // do minimization
  int trialcount=2;
  int Nconstraint = 16;
  double e[1];
  t1(0,0,x,e,0);
  Minimizer M(trialcount,sz,Nconstraint,xmin,xmax);
  M.func = t1;
  M.cFunc = cc;
  trialdata d21(M,"PHELAN-WEAIRE OPTIMIZATION");

  // experiment of f.
  /*
  for (int i=0;i<100;i++) {
    set_x(xmin,x,xmax,wslack,fslack);
    Minimizer N(trialcount,sz,Nconstraint,xmin,xmax);
    N.func = t1;
    N.cFunc = cc;
    N.optimize();
  for (int j=0;j<sz;j++) { x[j] = N.x[j]; }
    globalize_x(x);
    cout << "*** new trial " << endl;
    cout << "f[2][3] = " << f[2][3] << endl;
    cout << "f[1][3] = " << f[1][3] << endl;
    cout << "mu = " << mu() << endl << flush;
    //N.coutReport("ss");
  }
  */

    // report results
  for (int i=0;i<sz;i++) { x[i] = M.x[i]; }
  globalize_x(x);
    for (int i=0;i<Nconstraint;i++) {
      double r[1];
      cc(sz,i+1,x,r,0);
      cout << "constraint " << i << " is " << r[0] << endl;
    }
    cout << endl << endl;
    std::cout.precision(6);
    cout << "// NEW PASS ON PHELAN-WEAIRE: " << endl;
    cout << "t1 value before optimization = " << e[0] << endl;
    printglobal();
    cout << endl << endl << "mu " << mu() << endl;
    double totvol = 0.0;
    double totsurf = 0.0;
    for (int i=0;i<8;i++) {
      double lvol = volcell(wi[i],ww,kk[i],nn[i]);
      totvol += lvol;
      cout << "volcell " << i << " = " << lvol << endl;
    }
    cout << "total vol " << totvol << endl;
    cout << "det3 " << det3(f[0],f[1],f[2]) << endl;
    for (int i=0;i<8;i++) {
      double lsurf = surfcell(wi[i],ww,kk[i],nn[i]);
      totsurf += lsurf;
      cout << "surfcell " << i << " = " << lsurf << endl;
    }
    cout << "weightedmu " << weightedmu(x) << endl;
    cout << "fslack = " << fslack << endl;
    cout << "wslack = " << wslack << endl;
    //cout << "rhoslack = " << rhoslack << endl;
    report_near(xmin,x,xmax);
    cout.precision(24);
    cout << "mu " << mu() << endl;
    for (int i=0;i<30;i++) { cout << "//"; }
    cout << endl << endl;
    print_reduced_dih();
    // done
  }

