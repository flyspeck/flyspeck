// Test on Feb 16, 2012 to compute scaledVoronoi Phelan-Weaire foam.

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
    cout << v[i] << (i==n-1 ? "}" : ",");
  }
}


double norm(double x[3]) {
  return sqrt(x[0]*x[0]+x[1]*x[1]+x[2]*x[2]);
}

double dot(double x[3],double y[3]) {
  return x[0]*y[0] + x[1]*y[1] + x[2]*y[2];
}


double angle(double x[3],double y[3]) {
  return acos(dot (x,y)/ (norm(x) * norm(y)));
}

double square(double x) {
  return x*x;
}

void add3(double x[3],double y[3],double* ret) {
  for (int i=0;i<3;i++) { ret[i] = x[i] + y[i]; }
}

void scale(double s,double x[3],double* ret) {
  for (int i=0;i<3;i++) { ret[i] = x[i] * s; }
}

void sub3(double x[3],double y[3],double* ret) {
  for (int i=0;i<3;i++) { ret[i] = x[i] - y[i]; }
}

double dist2(double x[3],double y[3]) {
  double z[3];
  sub3(x,y,z);
  return dot(z,z);
}

double RvolAn(double x1, double x2, double x3,double x4,double x5, double x6) {
  return x1 * (x2 + x6 - x1) * chi(x4,x5,x3,x1,x2,x6)/ 
    (48.0 * U(x1,x2,x6) * sqrt (delta_x (x1,x2,x3,x4,x5,x6)));
}

double RsurfAn(double x1,double x2,double x3,double x4,double x5, double x6) {
  //cout << " sqrt " << sqrt(x1) << endl;
  return (RvolAn(x1,x2,x3,x4,x5,x6) * (6.0/sqrt(x1)));
}

double vol6(double x1,double x2,double x3, double x4, double x5,double x6) {
  return RvolAn(x1,x2,x3,x4,x5,x6) + RvolAn(x1,x3,x2,x4,x6,x5) +
    RvolAn(x2,x3,x1,x5,x6,x4) + RvolAn(x2,x1,x3,x5,x4,x6) +
    RvolAn(x3,x1,x2,x6,x4,x5) + RvolAn(x3,x2,x1,x6,x5,x4);
}

double surf6(double x1,double x2,double x3,double x4,double x5,double x6) {
   return RsurfAn(x1,x2,x3,x4,x5,x6) + RsurfAn(x1,x3,x2,x4,x6,x5) +
    RsurfAn(x2,x3,x1,x5,x6,x4) + RsurfAn(x2,x1,x3,x5,x4,x6) +
    RsurfAn(x3,x1,x2,x6,x4,x5) + RsurfAn(x3,x2,x1,x6,x5,x4);
}

double xp(double x1,double x2,double x6,double rho1,double rho2) {
  return (x1 * rho1 * rho1 + x2*rho2*rho2 - (x1 + x2 - x6) * rho1 * rho2);
}

// Analytic volume of the part of a  scaled Voronoi cell, inside a tetrahedron.
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

// Analytic external surface of the part of a  scaled Voronoi cell, inside a tetrahedron.
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

 double det3(double x[3],double y[3],double z[3]) {
   return (-x[2]*y[1]*z[0] + x[1]*y[2]*z[0] + x[2]*y[0]*z[1] 
	   - x[0]*y[2]*z[1] - x[1]*y[0]*z[2] + x[0]*y[1]*z[2]);
 }

 double volvector(double w0[3],double w1[3],double w2[3],double w3[3],
		  double rho1,double rho2,double rho3) {
   double x1 = dist2(w0,w1);
   double x2 = dist2(w0,w2);
   double x3 = dist2(w0,w3);
   double x4 = dist2(w2,w3);
   double x5 = dist2(w1,w3);
   double x6 = dist2(w1,w2);
   return vol6rho(x1,x2,x3,x4,x5,x6,rho1,rho2,rho3);
 }

 double surfvector(double w0[3],double w1[3],double w2[3],double w3[3],
		  double rho1,double rho2,double rho3) {
   double x1 = dist2(w0,w1);
   double x2 = dist2(w0,w2);
   double x3 = dist2(w0,w3);
   double x4 = dist2(w2,w3);
   double x5 = dist2(w1,w3);
   double x6 = dist2(w1,w2);
   return surf6rho(x1,x2,x3,x4,x5,x6,rho1,rho2,rho3);
 }

double getrho(double rho[54],int rr[54*2][2], int c,int j) {
  for (int i=0;i<54*2;i++) {
    if (rr[i][0]==c && rr[i][1] ==j)  
      return  (i % 2 == 0 ? rho[i/2] : (1.0/ rho[(i-1)/2])) ;
  }
  cout << "no match found " << c << " " << j << " " << (j % 8) << endl;
  for (int i=0;i<54*2;i++)  {
      cout << "rr " << rr[i][0] << "," << rr[i][1] << endl;
    }
  assert(1==0);
}

 // w0 cell center.
 // w[i] updated positions of other points.
 // rho[i], scaling factors.
 // k[i][0],k[i][1],k[i][2],  positions of triangles of dual polyhedron around w0,
 // n number of triangles. return the total volume,
double volcell(int c, double w0[3],double wr[27*8][3],double rho[54],int rr[54*2][2],int k[24][3],int n) {
   double sum = 0;
   for (int i=0;i<n;i++) {
     int j1 = k[i][0], j2 = k[i][1], j3 = k[i][2];
     double rho1 = getrho(rho,rr,c,j1);
     double rho2 = getrho(rho,rr,c,j2);
     double rho3 = getrho(rho,rr,c,j3);
     double t = volvector(w0,wr[j1],wr[j2],wr[j3],rho1,rho2,rho3);
     sum += t;
   }
   return sum;
 };;

double surfcell(int c,double w0[3],double wr[27*8][3],double rho[54],int rr[54*2][2],int k[24][3],int n) {
   double sum = 0;
   for (int i=0;i<n;i++) {
     int j1 = k[i][0], j2 = k[i][1], j3 = k[i][2];
     double rho1 = getrho(rho,rr,c,j1);
     double rho2 = getrho(rho,rr,c,j2);
     double rho3 = getrho(rho,rr,c,j3);
     sum += surfvector(w0,wr[j1],wr[j2],wr[j3],rho1,rho2,rho3);
   }
   return sum;
 };;

 // initial data
// 0.618 ==> volcell0 = 1.127, volcell1 = 0.88
// 0.55 ==> volcell0 = 1.03, volcell1 = 0.92.
// 0.5 ==> volcell0 = 0.9765, volcell1 = 0.9765.

/*
 double a = 0.5; // just rough initial guess, based on golden ratio of icos.
 double v0[3]={0,0,0};
 double v1[3]={1,1,1};
 double v2[3]={1,0,a};
 double v3[3]={1,0,-a};
 double v4[3]={a,1,0};
 double v5[3]={-a,1,0};
 double v6[3]={0,a,1};
 double v7[3]={0,-a,1};

 double e1[3]={2,0,0};
 double e2[3]={0,2,0};
 double e3[3]={0,0,2};
*/

// restart using numerical data from Ex10.
double v0[3]={3.32463046565594386e-31,1.13071491418928732e-30,1.36081683235910404e-30};
double v1[3]={0.999051115854998173,0.994596804663589129,0.966978075224307676};
double v2[3]={0.926427395381585694,0.0472955802039116413,0.506715705090871604};
double v3[3] = {0.935333171042378675,0.0253386857624800926,-0.461390986432040517};
double v4[3]={0.539614146986469256,1.00249974182614432,-0.0331459182626294355};
double v5[3]={-0.427177273120571521,0.99143929520656171,-0.0410868883618149203};
double v6[3]={-0.0270200998587204443,0.493907916765477017,0.936833355672711199};
double v7[3]={-0.0445201687349273331,-0.461485873582513861,0.927616642945689129};

double e1[3]={1.93374988681604743,-6.57389459969765301e-31,-2.32241161902254319e-31};
double e2[3]={0.0648757951738884592,1.92439245824388205,-1.39641537806812864e-30};
double e3[3]={1.84266964531742485e-31,0.0639952253948175148,1.93366450406431345};

double rhodata[54]={1.461,1.081,0.6728,0.9228,1.09,1.429,0.6988,0.9478,1.115,1.488,0.957,0.6867,0.9211,1.427,1.074,1.087,0.6829,1.487,1.464,0.9563,0.6739,0.9509,0.7002,1.117,1.038,0.8675,1.5,1.417,1.168,0.9422,1.152,0.8748,0.7187,0.6672,1.387,1.122,1.069,0.8774,0.8463,0.7058,1.184,0.9638,1.113,1.389,1.5,0.8762,0.6638,1.071,0.9362,1.166,0.7162,0.8765,0.6553,1.5};

// init once.  24=max number of dual triangles.
 int kk[8][24][3];   // kk[i][j] is a triple of indices of dual triangle face j of cell i. <=> vertex of sc.Vor.
 int nn[8]; // nn[i] is number of dual triangles (i.e. scVor vertices) on cell i.  (12 faces=>(nn=20, etc.)).
int  rr[54*2][2]; // {i,j} :  wi[i],ww[j] . rho[index/2]^{-1}.   inverse when index is odd. 
// runs over faces in fun. domain, indices for rhof.

 // global dynamic data

double wi[8][3];  // cell centers.
double f[3][3];  // lattice generators.

double rhof[54]; // number of shared faces in fundamental domain (2 x 12 + 6 x 14)/2.

 
 void initwif() {
   for (int i =0;i<3;i++) for (int j=0;j<3;j++) {
       f[i][j] = (i==0 ?e1[j] : (i==1 ? e2 [j] : e3[j]));
     }
   for (int i=0;i<8;i++) for (int j=0;j<3;j++) {
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
       for (int i=0;i<54;i++) { rhof[i]=rhodata[i];  }
 }
 }



double ww[27*8][3];  // coordinates of 8 centers, and their lattice translates by -1,0,1 in x,y,z


 void setww() {
   for (int i=0;i<3;i++) for (int j=0;j<3;j++) for (int k=0;k<3;k++)  for (int u=0;u<8;u++) {
	   double z[3]={0,0,0};
	   double s[3];
	   scale(i-1,f[0],s); add3(z,s,z);
	   scale(j-1,f[1],s); add3(z,s,z);
	   scale(k-1,f[2],s); add3(z,s,z);
	   add3(z,wi[u],z);
	   for (int p=0;p<3;p++) {
	     ww[u + 8*(i+3*j +9*k)][p] = z[p];
	   }
	 }
 }

int isnbr(double v[3],double w[3]) {
    double x1 = abs(v[0]-w[0]), x2 = abs(v[1]-w[1]), x3 = abs(v[2]-w[2]);
     return ((x1 < 1.1) && (x2 < 1.1 ) &&(x3 < 1.1) &&(dist2(v,w) > 0.01) &&
	     (dist2(v,w) < 2.1));
}

int isneg(double v1[3],double v2[3],double w1[3],double w2[3]) {
  double z1[3],z2[3],s[3];
  sub3(v1,v2,z1);
  sub3(w1,w2,z2);
  add3(z1,z2,s);
  return (abs(dot(s,s)) < 0.01);
}

int nr[8]; // number of nearest nbrs.
int ns[8][27*8]; // nearest nbrs

 void setkknn (int i) {
   int near=0;
   for (int j=0;j<27*8;j++) {
     assert(near < 27*8);
     if (isnbr(wi[i],ww[j])) {
       ns[i][near] = j; near++;
     }
   }
   nr[i]=near;
   cout << i << " has " << near << " neighbors" << endl;
   int kc = 0;
   for (int j1=0;j1<near;j1++) for (int j2=0;j2<near;j2++) for (int j3=0;j3<near;j3++) {
	 if (isnbr(ww[ns[i][j1]],ww[ns[i][j2]]) && isnbr(ww[ns[i][j2]],ww[ns[i][j3]]) && 
	     isnbr(ww[ns[i][j3]],ww[ns[i][j1]]) &&
	     (j1 < j2) && (j2 < j3)) {
	   kk[i][kc][0]=ns[i][j1]; kk[i][kc][1]=ns[i][j2]; kk[i][kc][2]=ns[i][j3]; kc++;
	 }
       }
   nn[i]=kc;
   cout << i << " has " << kc << " faces " << endl;
 }

void setrr() {
  cout << "entering set rr " << endl;
  int rc = 0;
  int N = 150;
  int table[N][2];
  for (int i=0;i<N;i++) for (int j=0;j<2;j++) {
      table[i][j] = 0;
    }
  for (int i=0;i<8;i++) for (int j=0;j<nr[i];j++) {
      assert(rc<N);
      table[rc][0] = i;
      table[rc][1] = ns[i][j];
      rc++;
    }
  int neg=0;
  for (int i=0;i<rc;i++) for (int j=i+1;j<rc;j++) {
      if (isneg(wi[table[i][0]],ww[table[i][1]],wi[table[j][0]],ww[table[j][1]]) &&
	  (table[i][0] % 8 == table[j][1] % 8) && (table[j][0] % 8 == table[i][1] % 8)) {
	for (int o = 0;o<2;o++) {
	  int k; 
	  for (int u = 0;u<2;u++) {
	    rr[2*neg+o][u] = table[ (o ? j : i) ][u];
	  }
	}
	neg++;
      }
    }
  cout << "rho faces found " << rc << endl;
  cout << "translates found " << neg << endl;
  // check integrity of  data.
 }

double totalsurface() {
  double sum = 0;
  for (int i=0;i<8;i++) {
    sum += surfcell(i,wi[i],ww,rhof,rr,kk[i],nn[i]);
  }
  return sum;
}

double mu() {
  double t = totalsurface()/(8.0 * 2.0);
  return (t*t*t);
}

void mkglobal(double* x) {
    for (int i=0;i<8;i++) for (int j=0;j<3;j++) {
      wi[i][j] = x[i + 8*j];
    }
  int offset = 8*3;
  for (int i=0;i<3;i++) for (int j=0;j<3;j++) {
      f[i][j] = x[offset+ i + 3 * j];
    }
  offset += 3*3;
  for (int i=0;i<54;i++) { 
      rhof[i] = x[offset + i];
    }
  offset += 54;
  setww();
}

double weightedmu(double* x) {
  mkglobal(x);
  double xf = 0.0; // was 1000.0
  double m = mu();
  for (int i =0;i<8;i++) {
    double t = 1.0- volcell(i,wi[i],ww,rhof,rr,kk[i],nn[i]);
    m += xf * t*t;
  }
  double t = det3(f[0],f[1],f[2]) - 8.0; 
  m+= xf * t * t;
  //cout << "mu " << m << endl;
  return m;
}

// this is minimized
void t1(int numargs,int whichFn,double* x,double* ret,void*) {
  *ret =  weightedmu(x);
};

// constraints 8 vol, + det3.

void cc(int numargs,int whichFn,double* x, double* ret,void*) {
  mkglobal(x);
  if (whichFn <= 8) {
    int i = whichFn - 1;
    *ret = 1.0- volcell(i,wi[i],ww,rhof,rr,kk[i],nn[i]);
  }
  else { *ret = det3(f[0],f[1],f[2]) - 8.0; }
}



void printglobal() {
  cout << "wi (coordinates)" << endl;
  for (int i=0;i<8;i++) {
    printv(wi[i],3);
    cout << endl;
    }
  cout << endl << "f (lattice)" << endl;
  for (int i=0;i<3;i++) {
    printv(f[i],3);
    cout << endl;
  }
  cout << endl << "rho " << endl;
  cout.precision(4);
  printv(rhof,54);
}

//double rho_init[] = {1.1,1.029,0.9918,0.9202,0.9189,0.9946,1.025,1.1,1.1,1.03,0.9927,0.9203,0.9921,1.026,0.919,1.1,1.025,1.1,0.9948,1.1,0.9203,0.9188,0.994,1.029,0.9705,1.015,1.1,1.031,0.9669,0.9278,1.083,1.034,0.9876,0.9022,1.012,0.9712,1.078,1.03,0.924,0.966,0.9852,1.035,0.9861,1.036,0.9023,0.9251,1.1,0.9682,1.027,1.08,0.968,1.013,0.902,1.1};

int main() {
    initwif();
    setww();
    for (int i=0;i<8;i++) {
      setkknn(i); }
    setrr();
    int sz = 8*3+3*3+54;
    double xmin[sz];
    double xmax[sz];
    double x[sz];
    int offset = 0;
    // set ww
    double wslack = 0.05;
    for (int i=0;i<8;i++) for (int j=0;j<3;j++) {
	xmin[offset + i + 8*j] = wi[i][j] - wslack;
	xmax[offset + i + 8*j] = wi[i][j] + wslack;
	x[offset + i + 8*j] = wi[i][j] ;
      }
    {
      int i=0;
      for (int j=0;j<3;j++) {
	xmin[offset+ i + 8*j] = wi[i][j];
	xmax[offset+ i + 8*j] = wi[i][j];
      }
    }
    offset += 8*3;
    // set f
    double fslack = 0.01;
    for (int i=0;i<3;i++) for (int j=0;j<3;j++) {
	int u = offset + i + 3 * j;
	x[u] = (i==0 ? e1[j]  : (i==1 ? e2[j] : e3[j]));
	xmin[u] = (j <= i ? x[u] - fslack : x[u]);
	xmax[u] = (j <= i ? x[u] + fslack: x[u]);
      }
    offset += 3*3;
    // set rho.
    double rhoslack = 1.05;
    for (int i=0;i<54;i++) { 
      xmin[offset + i] = rhodata[i]/rhoslack;
	xmax[offset + i] = rhodata[i]*rhoslack;
	x[offset + i] = rhodata[i];
      }
    offset += 54;
    int trialcount=5;
    assert(offset ==sz);


    double e[1];
    t1(0,0,x,e,0);
    cout << "t1 = " << e[0] << endl;

    // do minimization
    Minimizer M(trialcount,offset,9,xmin,xmax);
    M.func = t1;
    M.cFunc = cc;
    trialdata d21(M,"xxx");
    for (int i=0;i<offset;i++) { x[i] = M.x[i]; }

    for (int i=0;i<9;i++) {
      double r[1];
      cc(offset,i+1,x,r,0);
      mkglobal(x);
      cout << "constraint " << i << " is " << r[0] << endl;
    }

    std::cout << std::endl << std::endl;
    std::cout.precision(18);
    mkglobal(x);
    printglobal();
    cout.precision(24);
    cout << endl << endl << "mu " << mu() << endl;
    double totvol = 0.0;
    double totsurf = 0.0;
    for (int i=0;i<8;i++) {
      mkglobal(x);
      double lvol = volcell(i,wi[i],ww,rhof,rr,kk[i],nn[i]);
      double lsurf = surfcell(i,wi[i],ww,rhof,rr,kk[i],nn[i]);
      totvol += lvol;
      totsurf += lsurf;
      cout << "volcell " << i << " = " << lvol << endl;
      cout << "surfcell " << i << " = " << lsurf << endl;
    }
    cout << "total vol " << totvol << endl;
    cout << "weightedmu " << weightedmu(x) << endl;
    cout << "fslack = " << fslack << endl;
   cout << "wslack = " << wslack << endl;
    cout << "rhoslack = " << rhoslack << endl;
    cout << "mu " << mu() << endl;
  }

