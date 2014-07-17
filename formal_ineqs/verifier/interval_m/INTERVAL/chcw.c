/*
    Copyright 2011 Jean-Marc Alliot / Jean-Baptiste Gotteland

    This file is part of the ocaml interval library.

    The ocaml interval library is free software: 
    you can redistribute it and/or modify it under the terms of 
    the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    The ocaml interval library is distributed in the hope that it will be 
    useful,but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public 
    License along with the ocaml interval library. 
    If not, see <http://www.gnu.org/licenses/>.
*/

#include <fenv.h>
#include <stdarg.h>
#include <stdio.h>
#include <mlvalues.h>
#include <alloc.h>
#include <fail.h>
#include <memory.h>
#include <unistd.h>
#include <math.h>

/*
We work with _high and _low version of arithmetic functions.
Extreme care must be taken regarding inline assembly. As setting the mode of the 
processor has to be done before any computation, we have to prevent instructions 
reordering.
This is also true for setting back the mode to nearest: the result has to be stored
in the stack before setting the mode to nearest: computation is done in 80 bits mode
and casting the result to 64 bits has to be done before changing rounding mode 
because the casting itself introduces errors.
This is why some (artificial) variables dependencies have to be used, along with 
the "volatile" keyword and the "memory" keyword in the clobber list.
It is extremely wise to check the assembly code generated...
*/

/* Set the processor to different rounding modes */
#define SET_LOW(ref) "fstcw "#ref"\n\t andw $0xf3ff,"#ref"\n\t orw $0x0400,"#ref"\n\t fldcw "#ref"\n\t"
#define SET_HIGH(ref) "fstcw "#ref"\n\t andw $0xf3ff,"#ref"\n\t orw $0x0800,"#ref"\n\t fldcw "#ref"\n\t"
#define SET_NEAREST(ref) "fstcw "#ref"\n\t andw $0xf3ff,"#ref"\n\t fldcw "#ref"\n\t"

/*
Set the processor to use full 64+16 bits. Useful with long double, 
but VERY dangerous with ordinary doubles because optimization of the code by the 
compiler can give different results depending on the way the the computation was 
done (the x87 80 bits registers are stored in 64 bits memory locations)... 
This is the default with Linux.
*/
#define SET_64(ref) "fstcw "#ref"\n\t andw $0xfcff,"#ref"\n\t orw $0x0300,"#ref"\n\t fldcw "#ref"\n\t"
/*
Set the processor to use 53+11 bits. This is the standard for double in IEEE-754 
*/
#define SET_53(ref) "fstcw "#ref"\n\t andw $0xfcff,"#ref"\n\t orw $0x0200,"#ref"\n\t fldcw "#ref"\n\t"
/*
Set the processor to use 24+8 bits. IEEE-754 standard for float 
*/
#define SET_24(ref) "fstcw "#ref"\n\t andw $0xfcff,"#ref"\n\t fldcw "#ref"\n\t"

static short int cw;

void set_nearest() {
  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw));
}

void set_high() {
  asm __volatile__(SET_HIGH(%0)
		   :"=m"(cw));
}

void set_low() {
  asm __volatile__(SET_LOW(%0)
		   :"=m"(cw));
}

/* Infinity -------------------------------------------------------------------- */
long double infinity = 1.0/0.0;
long double neg_infinity = -1.0/0.0;

/* Int to float conversion ----------------------------------------------------- */
static long long int tmp;
#ifdef __linux
#define FILDQ   asm __volatile__("fildq tmp":"=t"(res):"m"(tmp):"memory")
#else
#define FILDQ   asm __volatile__("fildq _tmp":"=t"(res):"m"(tmp):"memory")
#endif

double ffloat(long int a) {
  double res;

  tmp = a;
  FILDQ;
  return(res);
}


double ffloat_low(long int a) {
  double res;

  tmp = a;
  asm __volatile__(SET_LOW(%0)
		   :"=m"(cw)
		   :"m"(tmp)
		   :"memory");
  FILDQ;
  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(res),"m"(tmp)
		   :"memory");
  return(res);
}

double ffloat_high(long int a) {
  double res;

  tmp = a;
  asm __volatile__(SET_HIGH(%0)
		   :"=m"(cw)
		   :"m"(tmp)
		   :"memory");
  FILDQ;
  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(res),"m"(tmp)
		   :"memory");
  return(res);
}


/* long double to double conversions ------------------------------------------ */

double to_low(long double a) {
  double res;

  asm __volatile__(SET_LOW(%0)
		   :"=m"(cw)
		   :"m"(res),"m"(a)
		   :"memory"
		   );
  res = a;
  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(res),"m"(a)
		   :"memory"
		   );
  return(res);
}

double to_high(long double a) {
  double res;

  asm __volatile__(SET_HIGH(%0)
		   :"=m"(cw)
		   :"m"(res),"m"(a)
		   :"memory");
  res = a;
  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(res),"m"(a)
		   :"memory");
  return(res);
}

/* fadd_l, fsub_l, fmul_l, fdiv_l --------------------------------------------- */
double fadd(double a, double b) {

  volatile double res;

  asm __volatile__("fadd %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");
  return(res);
}

double fadd_low(double a, double b) {

  volatile double res;

  asm __volatile__(SET_LOW(%3)
		   "fadd %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(cw)
		   :"memory");

  return(res);
}

double fadd_high(double a, double b) {

  volatile double res;

  asm __volatile__(SET_HIGH(%3)
		   "fadd %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(cw)
		   :"memory");

  return(res);
}

long double fadd_l(long double a, long double b) {

  long double res;

  asm __volatile__("fadd %%st(1),%%st(0)"
	       :"=t"(res)
	       :"0"(a),"u"(b),"m"(cw)
	       :"memory");

  return(res);
}

long double fadd_low_l(long double a, long double b) {

  long double res;

  asm __volatile__(SET_LOW(%3)
		   "fadd %%st(1),%%st(0)\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  return(res);
}

long double fadd_high_l(long double a, long double b) {

  long double res;

  asm __volatile__(SET_HIGH(%3)
		   "fadd %%st(1),%%st(0)\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  return(res);
}

double fsub(double a, double b) {

  volatile double res;

  asm __volatile__("fsub %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");
  return(res);
}

double fsub_low(double a, double b) {

  volatile double res;

  asm __volatile__(SET_LOW(%3)
		   "fsub %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(cw)
		   :"memory");

  return(res);
}

double fsub_high(double a, double b) {

  volatile double res;

  asm __volatile__(SET_HIGH(%3)
		   "fsub %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(cw)
		   :"memory");

  return(res);
}

long double fsub_l(long double a,long double b) {
  long double res;

  asm __volatile__("fsub %%st(1),%%st(0)"
	       :"=t"(res)
	       :"0"(a),"u"(b),"m"(cw)
	       :"memory");

  return(res);
}

long double fsub_low_l(long double a, long double b) {

  long double res;

  asm __volatile__(SET_LOW(%3)
		   "fsub %%st(1),%%st(0)\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  return(res);
}

long double fsub_high_l(long double a, long double b) {

  long double res;

  asm __volatile__(SET_HIGH(%3)
		   "fsub %%st(1),%%st(0)\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  return(res);
}

double fmul(double a, double b) {

  volatile double res;

  asm __volatile__("fmul %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");
  return(res);
}

double fmul_low(double a, double b) {

  volatile double res;

  asm __volatile__(SET_LOW(%3)
		   "fmul %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(cw)
		   :"memory");

  return(res);
}

double fmul_high(double a, double b) {

  volatile double res;

  asm __volatile__(SET_HIGH(%3)
		   "fmul %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(cw)
		   :"memory");

  return(res);
}

long double fmul_l(long double a, long double b) {
  long double res;

  asm __volatile__("fmul %%st(1),%%st(0)"
	       :"=t"(res)
	       :"0"(a),"u"(b),"m"(cw)
	       :"memory");

  return(res);
}

long double fmul_low_l(long double a, long double b) {

  long double res;

  asm __volatile__(SET_LOW(%3)
		   "fmul %%st(1),%%st(0)\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  return(res);
}

long double fmul_high_l(long double a, long double b) {

  long double res;

  asm __volatile__(SET_HIGH(%3)
		   "fmul %%st(1),%%st(0)\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  return(res);
}

double fdiv(double a, double b) {

  volatile double res;

  asm __volatile__("fdiv %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");
  return(res);
}

double fdiv_low(double a, double b) {

  volatile double res;

  asm __volatile__(SET_LOW(%3)
		   "fdiv %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(cw)
		   :"memory");

  return(res);
}

double fdiv_high(double a, double b) {

  volatile double res;

  asm __volatile__(SET_HIGH(%3)
		   "fdiv %%st(1),%%st(0)\n\t"
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  asm __volatile__(SET_NEAREST(%0)
		   :"=m"(cw)
		   :"m"(cw)
		   :"memory");

  return(res);
}

long double fdiv_l(long double a,long double b) {
  long double res;

  asm __volatile__("fdiv %%st(1),%%st(0)"
	       :"=t"(res)
	       :"0"(a),"u"(b),"m"(cw)
	       :"memory");

  return(res);
}

long double fdiv_low_l(long double a, long double b) {

  long double res;

  asm __volatile__(SET_LOW(%3)
		   "fdiv %%st(1),%%st(0)\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  return(res);
}

long double fdiv_high_l(long double a, long double b) {

  long double res;

  asm __volatile__(SET_HIGH(%3)
		   "fdiv %%st(1),%%st(0)\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  return(res);
}

/* fprem_l, fprem1_l: exact result of a mod b, with quadrant information ------- */

long double fprem_l(long double a, long double b) {
  long double res;

  asm ("1: fprem\n\t"
       "fstsw %%ax\n\t"
       "testw $0x400,%%ax\n\t"
       "jnz 1b\n\t"
       :"=t"(res)
       :"0"(a),"u"(b)
       :"%ax","%cc");
  return(res);
}

void fprem1_l(long double a, long double b, long double *r, int *q) {
  long double res;
  short int res2;

  asm __volatile__("1: fprem1\n\t"
		   "fstsw %%ax\n\t"
		   "testw $0x400,%%ax\n\t"
		   "jnz 1b\n\t"
		   :"=t"(res),"=a"(res2)
		   :"0"(a),"u"(b)
		   :"%cc");
  *r=res;
  *q=((res2&0x100)>>6)+((res2&0x4000)>>13)+((res2&0x200)>>9);
}

/* fsqrt_l --------------------------------------------------------------------- */

long double fsqrt_l(long double a) {
  long double res;
  asm ("fsqrt":"=t"(res):"0"(a));
  return(res);
}

long double fsqrt_low_l(long double a) {
  long double res;

  asm __volatile__(SET_LOW(%2)
		   "fsqrt\n\t"
		   SET_NEAREST(%2)
		   :"=t"(res)
		   :"0"(a),"m"(cw)
		   :"memory");

  return(res);
}

long double fsqrt_high_l(long double a) {
  long double res;

  asm __volatile__(SET_HIGH(%2)
		   "fsqrt\n\t"
		   SET_NEAREST(%2)
		   :"=t"(res)
		   :"0"(a),"m"(cw)
		   :"memory");

  return(res);
}

/* flog_l ---------------------------------------------------------------------- */

long double flog_l(long double a) {
  long double res;

  asm ("fldln2\n\t" /* ln(2) a */
       "fxch\n\t"   /* a ln(2) */
       "fyl2x\n\t"  /* ln(2)*log2(a) = ln(a) */
       :"=t"(res)
       :"0"(a)
       :"%st(7)"); /*We push one level of the stack, thus clobbering st(7) */
  return(res);
}

long double flog_low_l(long double a) {
  long double res;

  asm __volatile__(SET_LOW(%2)
		   "fldln2\n\t"
		   "fxch\n\t"
		   "fyl2x\n\t"
		   SET_NEAREST(%2)
		   :"=t"(res)
		   :"0"(a),"m"(cw)
		   :"%st(7)");

  return(res);
}

long double flog_high_l(long double a) {
  long double res;

  asm __volatile__(SET_HIGH(%2)
		   "fldln2\n\t"
		   "fxch\n\t"
		   "fyl2x\n\t"
		   SET_NEAREST(%2)
		   :"=t"(res)
		   :"0"(a),"m"(cw)
		   :"%st(7)");

  return(res);
}


/* fexp_l --------------------------------------------------------------------- */

long double fexp_l(long double a) {
  long double res;

  if (a== infinity) {return infinity;}
  else if (a == neg_infinity) {return 0.;};
  asm __volatile__("fldl2e\n\t"                /* log2(e) a */
		   "fmulp   %%st, %%st(1)\n\t" /* a*log2(e) */
		   "fld     %%st(0)\n\t"       /* a*log2(e) a*log2(e) */
		   "frndint\n\t"               /* int(a*log2(e)) a*log2(e) */
		   "fsubr   %%st, %%st(1)\n\t" /* int(a*log2(e)) frac(a*log2(e)) */
		   "fxch\n\t"                  /* frac(a*log2(e)) int(a*log2(e)) */
		   "f2xm1\n\t"                 /* 2^frac(a*log2(e))-1 int(...)  */
		   "fld1\n\t"                  /* 1 2^frac(a*log2(e))-1 int(...)  */
		   "faddp   %%st, %%st(1)\n\t" /* 2^frac(a*log2 e) int(...)  */
		   "fscale\n\t"                /* 2^frac(...)*2^int(...) */
		   "fstp    %%st(1)\n\t"
		   :"=t"(res)
		   :"0"(a)
		   :"%st(6)","%st(7)");  /* We push two levels on the stack, thus clobbering st(6) and st(7) */

  return(res);
}

long double fexp_low_l(long double a) {
  long double res;

  if (a == infinity) {return infinity;}
  else if (a == neg_infinity) {return 0.;}
  else if (0.0 <= a) {
    asm __volatile__(SET_LOW(%2)
		     "fldl2e\n\t"
		     "fmulp   %%st, %%st(1)\n\t"
		     "fld     %%st(0)\n\t"
		     "frndint\n\t"
		     "fsubr   %%st, %%st(1)\n\t"
		     "fxch\n\t"
		     "f2xm1\n\t"
		     "fld1\n\t"
		     "faddp   %%st, %%st(1)\n\t"
		     "fscale\n\t"
		     "fstp    %%st(1)\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(6)","%st(7)");
  }
  else {
    asm __volatile__(SET_HIGH(%2)
		     "fldl2e\n\t"
		     SET_LOW(%2)
		     "fmulp   %%st, %%st(1)\n\t"
		     "fld     %%st(0)\n\t"
		     "frndint\n\t"
		     "fsubr   %%st, %%st(1)\n\t"
		     "fxch\n\t"
		     "f2xm1\n\t"
		     "fld1\n\t"
		     "faddp   %%st, %%st(1)\n\t"
		     "fscale\n\t"
		     "fstp    %%st(1)\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(6)","%st(7)");
  }
  return(res);
}

long double fexp_high_l(long double a) {
  long double res;

  if (a == infinity) {return infinity;}
  else if (a == neg_infinity) {return 0.;}
  else if (0.0 <= a) {
    asm __volatile__(SET_HIGH(%2)
		     "fldl2e\n\t"
		     "fmulp   %%st, %%st(1)\n\t"
		     "fld     %%st(0)\n\t"
		     "frndint\n\t"
		     "fsubr   %%st, %%st(1)\n\t"
		     "fxch\n\t"
		     "f2xm1\n\t"
		     "fld1\n\t"
		     "faddp   %%st, %%st(1)\n\t"
		     "fscale\n\t"
		     "fstp    %%st(1)\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(6)","%st(7)");
  }
  else {
    asm __volatile__(SET_LOW(%2)
		     "fldl2e\n\t"
		     SET_HIGH(%2)
		     "fmulp   %%st, %%st(1)\n\t"
		     "fld     %%st(0)\n\t"
		     "frndint\n\t"
		     "fsubr   %%st, %%st(1)\n\t"
		     "fxch\n\t"
		     "f2xm1\n\t"
		     "fld1\n\t"
		     "faddp   %%st, %%st(1)\n\t"
		     "fscale\n\t"
		     "fstp    %%st(1)\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(6)","%st(7)");
  }
  return(res);
}

/* flog_pow_l ------------------------------------------------------------------ */

long double flog_pow_l(long double a, long double b) {
  long double res;

  asm ("fyl2x\n\t"              /* b*log2(a) */
       "fld %%st(0)\n\t"        /* b*log2(a) b*log2(a) */
       "frndint\n\t"            /* int(b*log2(a)) b*log2(a) */
       "fsubr %%st,%%st(1)\n\t" /* int(b*log2(a)) frac(b*log2(a)) */
       "fxch\n\t"               /* frac(b*log2(a)) int(b*log2(a)) */
       "f2xm1\n\t"              /* 2^frac(b*log2(a))-1 int(b*log2(a)) */
       "fld1\n\t"               /* 1 2^frac(b*log2(a))-1 int(b*log2(a)) */
       "faddp %%st,%%st(1)\n\t" /* 2^frac(b*log2(a)) int(b*log2(a)) */
       "fscale"                 /* 2^(b*log2(a)) */
       :"=t"(res)
       :"0"(a),"u"(b)
       :"%st(7)"); /* We push one level of the stack (start with 2 levels, max 3: line fld1) */
  return(res);
}

long double flog_pow_low_l(long double a, long double b) {

  long double res;

  asm __volatile__(SET_LOW(%3)
		   "fyl2x\n\t"
		   "fld %%st(0)\n\t"
		   SET_NEAREST(%3)
		   "frndint\n\t"
		   SET_LOW(%3)
		   "fsubr %%st,%%st(1)\n\t"
		   "fxch\n\t"
		   "f2xm1\n\t"
		   "fld1\n\t"
		   "faddp %%st,%%st(1)\n\t"
		   "fscale\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory","%st(7)");

  return(res);
}

long double flog_pow_high_l(long double a, long double b) {
  long double res;


  asm __volatile__(SET_HIGH(%3)
		   "fyl2x\n\t"
		   "fld %%st(0)\n\t"
		   SET_NEAREST(%3)
		   "frndint\n\t"
		   SET_HIGH(%3)
		   "fsubr %%st,%%st(1)\n\t"
		   "fxch\n\t"
		   "f2xm1\n\t"
		   "fld1\n\t"
		   "faddp %%st,%%st(1)\n\t"
		   "fscale\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory","%st(7)");

  return(res);
}

/* facos, fasin, fatan -------------------------------------------------------- */

long double facos_l(long double a) {
  long double res;
  asm ("fld %%st(0)\n\t"          /* a a */
       "fld1\n\t"                 /* 1 a a */
       "fsubp\n\t"                /* a-1 a */
       "fxch\n\t"                 /* a a-1 */
       "fld1\n\t"                 /* 1 a a-1 */
       "faddp\n\t"                /* a+1 a-1 */
       "fdivp\n\t"                /* (a+1)/(a-1) */
       "fsqrt\n\t"                /* sqrt((a+1)/(a-1)) */
       "fld1\n\t"                 /* 1 sqrt((a+1)/(a-1)) */
       "fxch\n\t"                 /* sqrt((a+1)/(a-1)) 1 */
       "fpatan\n\t"               /* atan(1/sqrt((a+1)/(a-1)) */
       "fld1\n\t"                 /* 1 atan(1/sqrt((a+1)/(a-1)) */
       "fadd %%st(0),%%st(0)\n\t" /* 2 atan(1/sqrt((a+1)/(a-1)) */
       "fmulp\n\t"                /* 2*atan(1/sqrt((a+1)/(a-1)) */
       :"=t"(res)
       :"0"(a)
       :"%st(7)","%st(6)"); /* Start with 1, max 3 : 2 clobbered */
  return(res);
}

long double facos_low_l(long double a) {
  long double res;

 asm __volatile__(SET_LOW(%2)
		  "fld %%st(0)\n\t"          /* a a */
		  "fld1\n\t"                 /* 1 a a */
		  "fsubp\n\t"                /* a-1 a */
		  "fxch\n\t"                 /* a a-1 */
		  "fld1\n\t"                 /* 1 a a-1 */
		  SET_HIGH(%2)               /* HIGH */
		  "faddp\n\t"                /* a+1 a-1 */
		  "fdivp\n\t"                /* (a+1)/(a-1) */
		  "fsqrt\n\t"                /* sqrt((a+1)/(a-1)) */
		  "fld1\n\t"                 /* 1 sqrt((a+1)/(a-1)) */
		  "fxch\n\t"                 /* sqrt((a+1)/(a-1)) 1 */
		  SET_LOW(%2)                /* LOW */
		  "fpatan\n\t"               /* atan(1/sqrt((a+1)/(a-1)) */
		  "fld1\n\t"                 /* 1 atan(1/sqrt((a+1)/(a-1)) */
		  "fadd %%st(0),%%st(0)\n\t" /* 2 atan(1/sqrt((a+1)/(a-1)) */
		  "fmulp\n\t"                /* 2*atan(1/sqrt((a+1)/(a-1)) */
		  SET_NEAREST(%2)
		  :"=t"(res)
		  :"0"(a),"m"(cw)
		  :"%st(7)","%st(6)");

 return(res);
}

long double facos_high_l(long double a) {
  long double res;


 asm __volatile__(SET_HIGH(%2) /* HIGH */
		  "fld %%st(0)\n\t"          /* a a */
		  "fld1\n\t"                 /* 1 a a */
		  "fsubp\n\t"                /* a-1 a */
		  "fxch\n\t"                 /* a a-1 */
		  "fld1\n\t"                 /* 1 a a-1 */
		  SET_LOW(%2)                /* LOW */
		  "faddp\n\t"                /* a+1 a-1 */
		  "fdivp\n\t"                /* (a+1)/(a-1) */
		  "fsqrt\n\t"                /* sqrt((a+1)/(a-1)) */
		  "fld1\n\t"                 /* 1 sqrt((a+1)/(a-1)) */
		  "fxch\n\t"                 /* sqrt((a+1)/(a-1)) 1 */
		  SET_HIGH(%2)               /* HIGH */
		  "fpatan\n\t"               /* atan(1/sqrt((a+1)/(a-1)) */
		  "fld1\n\t"                 /* 1 atan(1/sqrt((a+1)/(a-1)) */
		  "fadd %%st(0),%%st(0)\n\t" /* 2 atan(1/sqrt((a+1)/(a-1)) */
		  "fmulp\n\t"                /* 2*atan(1/sqrt((a+1)/(a-1)) */
		  SET_NEAREST(%2)
		  :"=t"(res)
		  :"0"(a),"m"(cw)
		  :"%st(7)","%st(6)");

 return(res);
}

long double fasin_l(long double a) {
  long double res;
  asm ("fld %%st(0)\n\t"          /* a a */
       "fmul %%st(1),%%st(0)\n\t" /* a2 a */
       "fld1\n\t"                 /* 1 a2 a */
       "fsubp\n\t"                /* 1-a2 a */
       "fsqrt\n\t"                /* sqrt(1-a2) a */
       "fpatan\n\t"               /* atan(a/sqrt(1-a2)) */
       :"=t"(res)
       :"0"(a)
       :"%st(7)");
  return(res);
}

long double fasin_low_l(long double a) {
  long double res;

  if (a>0) {
    asm __volatile__(SET_LOW(%2)
		     "fld %%st(0)\n\t"
		     "fmul %%st(1),%%st(0)\n\t"
		     SET_HIGH(%2)
		     "fld1\n\t"
		     "fsubp\n\t"
		     "fsqrt\n\t"
		     SET_LOW(%2)
		     "fpatan\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(7)");
    return(res);
  }
  else {
    asm __volatile__(SET_HIGH(%2)
		     "fld %%st(0)\n\t"
		     "fmul %%st(1),%%st(0)\n\t"
		     SET_LOW(%2)
		     "fld1\n\t"
		     "fsubp\n\t"
		     "fsqrt\n\t"
		     "fpatan\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(7)");
    return(res);
  }
}

long double fasin_high_l(long double a) {
  long double res;

  if (a>0)  {
    asm __volatile__(SET_HIGH(%2)
		     "fld %%st(0)\n\t"
		     "fmul %%st(1),%%st(0)\n\t"
		     SET_LOW(%2)
		     "fld1\n\t"
		     "fsubp\n\t"
		     "fsqrt\n\t"
		     SET_HIGH(%2)
		     "fpatan\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(7)");
    return(res);
  }
  else {
    asm __volatile__(SET_LOW(%2)
		     "fld %%st(0)\n\t"
		     "fmul %%st(1),%%st(0)\n\t"
		     SET_HIGH(%2)
		     "fld1\n\t"
		     "fsubp\n\t"
		     "fsqrt\n\t"
		     "fpatan\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(7)");
    return(res);
  }
}

long double fatan_l(long double a, long double b) {
  long double res;
  asm ("fpatan":"=t"(res):"0"(a),"u"(b));
  return(res);
}

long double fatan_low_l(long double a, long double b) {
  long double res;

  asm __volatile__(SET_LOW(%3)
		   "fpatan\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");
  return(res);
}

long double fatan_high_l(long double a, long double b) {
  long double res;

  asm __volatile__(SET_HIGH(%3)
		   "fpatan\n\t"
		   SET_NEAREST(%3)
		   :"=t"(res)
		   :"0"(a),"u"(b),"m"(cw)
		   :"memory");

  return(res);
}

/* fcos_l, fsin_l, ftan_l ------------------------------------------------------ */
/* Assuming that, with long doubles:
   - When |a| <= pi/4, the simple double rounding of fsin_l(a) and fcos_l(a)
     in low (resp. high) modes gives a lower (resp. upper) bound
   - When 0 <= a < 2**63 :
   - a mod TwoPi_low and a mod TwoPi_high are in the same quadrant
   - a mod Pio2_high <= a mod pi/2 <= a mod Pio2_low
*/

#define Pio2_low   1.570796326794896619147984262454L
#define Pio2_high  1.570796326794896619256404479704L
#define Pi_low     3.141592653589793238295968524909L
#define Pi_high    3.141592653589793238512808959407L
#define TwoPi_low  6.283185307179586476591937049818L
#define TwoPi_high 6.283185307179586477025617918812L
#define Two63      9223372036854775808.0L

/* fcos, fsin, ftan in nearest mode */

long double fcos_l(long double a) {
  long double res;

  asm __volatile__("fcos\n\t"
		   :"=t"(res)
		   :"0"(a)
		   :"memory");

  return(res);
}

long double fsin_l(long double a) {
  long double res;

  asm __volatile__("fsin\n\t"
		   :"=t"(res)
		   :"0"(a)
		   :"memory");

  return(res);
}

long double ftan_l(long double a) {
  long double res;

  asm __volatile__ ("fptan\n\t"
		    "ffree %%st(0)\n\t"
		    "fincstp"
		    :"=t"(res)
		    :"0"(a)
		    :"%st(7)");

  return(res);
}

/* reductions to [-pi/4; pi/4] */

long double fcos_reduction(long double ra, int qa) {
  switch(qa) {
  case 0: {return(fcos_l(ra));}
  case 1: {return(-fsin_l(ra));}
  case 2: {return(-fcos_l(ra));}
  case 3: {return(fsin_l(ra));}
  }
  caml_failwith("fcos_reduction");
}

long double fsin_reduction(long double ra, int qa) {
  switch(qa) {
  case 0: {return(fsin_l(ra));}
  case 1: {return(fcos_l(ra));}
  case 2: {return(-fsin_l(ra));}
  case 3: {return(-fcos_l(ra));}
  }
  caml_failwith("fsin_reduction");
}

/* fcos, fsin, ftan in low / high modes --------------------------------------- */

long double fcos_low_l(long double la) {
  long double ra;
  int qa;

  if (la < 0.0) {la = -la;}
  fprem1_l(la, Pio2_low, &ra, &qa); /* ra = mod_high(la, pi/2) */
  qa = qa % 4;
  if (((qa == 2) && (0.0 < ra)) || (qa == 3) || ((qa == 0) && (ra < 0.0))) {
    fprem1_l(la, Pio2_high, &ra, &qa);
    qa = qa % 4;
  }
  return(fcos_reduction(ra, qa));
}

long double fcos_high_l(long double la) {
  long double ra;
  int qa;

  if (la < 0.0) {la = -la;}
  fprem1_l(la, Pio2_high, &ra, &qa); /* ra = mod_low(la, pi/2) */
  qa = qa % 4;
  if (((qa == 2) && (0.0 < ra)) || (qa == 3) || ((qa == 0) && (ra < 0.0))) {
    fprem1_l(la, Pio2_low, &ra, &qa);
    qa = qa % 4;
  }
  return(fcos_reduction(ra, qa));
}

long double fsin_high_l(long double la);

long double fsin_low_l(long double la) {
  long double ra;
  int qa;

  if (la < 0.0) {return(-fsin_high_l(-la));}
  fprem1_l(la, Pio2_high, &ra, &qa); /* ra = mod_low(la, pi/2) */
  qa = qa % 4;
  if (((qa == 1) && (0.0 < ra)) || (qa == 2) || ((qa == 3) && (ra < 0.0))) {
    fprem1_l(la, Pio2_low, &ra, &qa); /* ra = mod_high(la, pi/2) */
    qa = qa % 4;
  }
  return(fsin_reduction(ra, qa));
}

long double fsin_high_l(long double la) {
  long double ra;
  int qa;

  if (la < 0.0) {return(-fsin_low_l(-la));}
  fprem1_l(la, Pio2_low, &ra, &qa); /* ra = mod_high(la, pi/2 */
  qa = qa % 4;
  if (((qa == 1) && (0.0 < ra)) || (qa == 2) || ((qa == 3) && (ra < 0.0))) {
    fprem1_l(la, Pio2_high, &ra, &qa); /* ra = mod_low(la, pi/2) */
    qa = qa % 4;
  }
  return(fsin_reduction(ra, qa));
}

long double ftan_high_l(long double a);

long double ftan_low_l(long double a) {
  long double r;
  int q;

  if (a < 0.0) {return(-ftan_high_l(-a));}
  fprem1_l(a, Pio2_high, &r, &q);
  if ((q & 1) == 0) {return(ftan_l(r));}
  else {return(fdiv_low_l(1.0, ftan_l(-r)));}
}

long double ftan_high_l(long double a) {
  long double r;
  int q;

  if (a < 0.0) {return(-ftan_low_l(-a));}
  fprem1_l(a, Pio2_low, &r, &q);
  if ((q & 1) == 0) {return(ftan_l(r));}
  else {return(fdiv_high_l(1.0, ftan_l(-r)));}
}

/* fcos_I, fsin_I - with computation optimization ------------------------------ */

long double fcos_low_aux(long double la, long double ra) {
  int qa;
  if (la < 0.0) {la = -la; ra = -ra;}
  if (0.0 < ra) {fprem1_l(la, Pio2_low, &ra, &qa);}
  else {fprem1_l(la, Pio2_high, &ra, &qa);}
  qa = qa % 4;
  return(fcos_reduction(ra, qa));
}

long double fcos_high_aux(long double la, long double ra) {
  int qa;

  if (la < 0.0) {la = -la; ra = -ra;}
  if (0.0 < ra) {fprem1_l(la, Pio2_high, &ra, &qa);}
  else {fprem1_l(la, Pio2_low, &ra, &qa);}
  qa = qa % 4;
  return(fcos_reduction(ra, qa));
}

long double fsin_high_aux(long double la, long double ra);

long double fsin_low_aux(long double la, long double ra) {
  int qa;
  if (la < 0.0) {return(-fsin_high_aux(-la, -ra));}
  if ((-Pio2_high < ra) && (ra < Pio2_high)) {fprem1_l(la, Pio2_high, &ra, &qa);}
  else {fprem1_l(la, Pio2_low, &ra, &qa);}
  qa = qa % 4;
  return(fsin_reduction(ra, qa));
}

long double fsin_high_aux(long double la, long double ra) {
  int qa;

  if (la < 0.0) {return(-fsin_low_aux(-la, -ra));}
  if ((-Pio2_high < ra) && (ra < Pio2_high)) {fprem1_l(la, Pio2_low, &ra, &qa);}
  else {fprem1_l(la, Pio2_high, &ra, &qa);}
  qa = qa % 4;
  return(fsin_reduction(ra, qa));
}

void fcos_I(long double a, long double b, double *rra, double *rrb) {
  long double ra, rb;
  int qa, qb;

  if ((-Two63 < a) && (b < Two63) && (fsub_high_l(b, a) <= TwoPi_low)) {
    fprem1_l(a, TwoPi_low, &ra, &qa);
    fprem1_l(b, TwoPi_low, &rb, &qb);
    if (0 <= ra) {
      if (0 <= rb) {
	if (ra <= rb) {
	  *rra = to_low(fcos_low_aux(b, rb));
	  *rrb = to_high(fcos_high_aux(a, ra));
	  return;
	}
      }
      else {
	*rra = -1.0;
	if (ra <= -rb) {*rrb = to_high(fcos_high_aux(a, ra));}
	else {*rrb = to_high(fcos_high_aux(b, rb));}
	return;
      }
    } else {
      if (0 <= rb) {
	*rrb = 1.0;
	if (ra <= -rb) {*rra = to_low(fcos_low_aux(a, ra));}
	else {*rra = to_low(fcos_low_aux(b, rb));}
	return;
      } else {
	if (ra <= rb) {
	  *rra = to_low(fcos_low_aux(a, ra));
	  *rrb = to_high(fcos_high_aux(b, rb));
	  return;
	}
      }
    }
  }
  *rra = -1.0;
  *rrb = 1.0;
}

void fsin_I(long double a, long double b, double *rra, double *rrb) {
  long double ra, rb;
  int qa, qb;

  if ((-Two63 < a) && (b < Two63) && (fsub_high_l(b, a) < TwoPi_low)) {
    fprem1_l(a, TwoPi_low, &ra, &qa);
    fprem1_l(b, TwoPi_low, &rb, &qb);
    if (ra < -Pio2_low) {ra = ra + TwoPi_low;}
    if (rb < -Pio2_low) {rb = rb + TwoPi_low;}
    if (ra <= Pio2_low) {
      if (rb <= Pio2_low) {
	if (ra <= rb) {
	  *rra = to_low(fsin_low_aux(a, ra));
	  *rrb = to_high(fsin_high_aux(b, rb));
	  return;
	}
      }
      else {
	*rrb = 1.0;
	if (ra <= Pi_low - rb) {*rra = to_low(fsin_low_aux(a, ra));}
	else {*rra = to_low(fsin_low_aux(b, rb));}
	return;
      }
    }
    else {
      if (rb <= Pio2_low) {
	*rra = -1.0;
	if (rb <= Pi_low - ra) {*rrb = to_high(fsin_high_aux(a, ra));}
	else {*rrb = to_high(fsin_high_aux(b, rb));}
	return;
      }
      else {
	if (ra <= rb) {
	  *rra = to_low(fsin_low_aux(b, rb));
	  *rrb = to_high(fsin_high_aux(a, ra));
	  return;
	}
      }
    }
  }
  *rra = -1.0;
  *rrb = 1.0;
}

/* fcosh_l, fsinh_l, ftanh_l --------------------------------------------------- */

/* e^x-1 */

long double fexm1_l(long double a) {
  long double res;

  if ((a < -0.6) || (0.6 < a)) {
    return(fsub_l(fexp_l(a), 1.0));
  }
  else {
    asm __volatile__("fldl2e\n\t"                /* log2(e) a */
		     "fmulp   %%st, %%st(1)\n\t" /* a*log2(e) */
		     "f2xm1\n\t"                 /* 2^(a*log2(e))-1 */
		     :"=t"(res)
		     :"0"(a)
		     :"%st(7)");
    return(res);
  }
}

long double fexm1_low_l(long double a) {
  long double res;

  if ((a < -0.6) || (0.6 < a)) {
    return(fsub_low_l(fexp_low_l(a), 1.0));
  }
  else if (0.0 <= a) {
    asm __volatile__(SET_LOW(%2)
		     "fldl2e\n\t"
		     "fmulp   %%st, %%st(1)\n\t"
		     "f2xm1\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(7)");
    return(res);
  }
  else {
    asm __volatile__(SET_HIGH(%2)
		     "fldl2e\n\t"
		     SET_LOW(%2)
		     "fmulp   %%st, %%st(1)\n\t"
		     "f2xm1\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(7)");
    return(res);
  }
}

long double fexm1_high_l(long double a) {
  long double res;

  if ((a < -0.6) || (0.6 < a)) {
    return(fsub_high_l(fexp_high_l(a), 1.0));
  }
  else if (0.0 <= a) {
    asm __volatile__(SET_HIGH(%2)
		     "fldl2e\n\t"
		     "fmulp   %%st, %%st(1)\n\t"
		     "f2xm1\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(7)");
    return(res);
  }
  else {
    asm __volatile__(SET_LOW(%2)
		     "fldl2e\n\t"
		     SET_HIGH(%2)
		     "fmulp   %%st, %%st(1)\n\t"
		     "f2xm1\n\t"
		     SET_NEAREST(%2)
		     :"=t"(res)
		     :"0"(a),"m"(cw)
		     :"%st(7)");
    return(res);
  }
}

long double fcosh_l(long double a) {
  if ((a == infinity) || (a == neg_infinity)) {return(infinity);}
  else {return(fdiv_l(fadd_l(fexp_l(a), fexp_l(-a)), 2.0));}
}

long double fcosh_low_l(long double a) {
  long double res;
  if ((a == infinity) || (a == neg_infinity)) {return(infinity);}
  else {
    res = fdiv_low_l(fadd_low_l(fexp_low_l(a), fexp_low_l(-a)), 2.0);
    if (res < 1.) {return(1.);} else {return(res);}
  }
}

long double fcosh_high_l(long double a) {
  if ((a == infinity) || (a == neg_infinity)) {return(infinity);}
  else {return(fdiv_high_l(fadd_high_l(fexp_high_l(a), fexp_high_l(-a)), 2.0));}
}

long double fsinh_l(long double a) {
  if (a == infinity || (a == neg_infinity)) {return(a);}
  else if (a < 0.0) {return(-fdiv_l(-fexm1_l(2.0 * a), 2.0 * fexp_l(a)));}
  else {return(fdiv_l(-fexm1_l(-2.0 * a), 2.0 * fexp_l(-a)));}
}

long double fsinh_low_l(long double a) {
  if (a == infinity || (a == neg_infinity)) {return(a);}
  else if (a < 0.) {
    return(-fdiv_high_l(-fexm1_low_l(fmul_low_l(2.0, a)),
			fmul_low_l(2.0, fexp_low_l(a))));
  }
  else {
    return(fdiv_low_l(-fexm1_high_l(fmul_high_l(-2.0, a)),
		      fmul_high_l(2.0, fexp_high_l(-a))));
  }
}

long double fsinh_high_l(long double a) {
  if (a == infinity || (a == neg_infinity)) {return(a);}
  else if (a == neg_infinity) {return(neg_infinity);}
  else if (a < 0.) {
    return(-fdiv_low_l(-fexm1_high_l(fmul_high_l(2.0, a)),
		       fmul_high_l(2.0, fexp_high_l(a))));
  }
  else {
    return(fdiv_high_l(-fexm1_low_l(fmul_low_l(-2.0, a)),
		       fmul_low_l(2.0, fexp_low_l(-a))));
  }
}

long double ftanh_l(long double a) {
  long double em2xm1;

  if (a == infinity) {return(1.0);}
  else if (a == neg_infinity) {return(-1.0);}
  else {
    em2xm1 = fexm1_l(-fmul_l(2.0, a));
    if (em2xm1 == infinity) {return(-1.0);}
    else if (em2xm1 == neg_infinity) {return(1.0);}
    else {return(fdiv_l(-em2xm1, fadd_l(em2xm1, 2)));};
  }
}

long double ftanh_low_l(long double a) {
  long double em2xm1_high;

  if (a == infinity) {return(1.0);}
  else if (a == neg_infinity) {return(-1.0);}
  else {
    em2xm1_high = fexm1_high_l(fmul_high_l(-2.0, a));
    if (em2xm1_high == infinity) {return(-1.0);}
    else if (em2xm1_high == neg_infinity) {return(1.0);}
    else {return(fdiv_low_l(-em2xm1_high, fadd_high_l(em2xm1_high, 2.0)));};
  }
}

long double ftanh_high_l(long double a) {
  long double em2xm1_high;

  /* return -ftanh_low_l(-a);*/
  if (a == infinity) {return(1.0);}
  else if (a == neg_infinity) {return(-1.0);}
  else {
    em2xm1_high = fexm1_high_l(fmul_high_l(2.0, a));
    if (em2xm1_high == infinity) {return(1.0);}
    else if (em2xm1_high == neg_infinity) {return(-1.0);}
    return(-fdiv_low_l(-em2xm1_high, fadd_high_l(em2xm1_high, 2.0)));
  }
}

/* CAML ---------------------------------------------------------------------- */

value ffloat_caml(value a) {
  return(caml_copy_double(ffloat(Long_val(a))));
}

value ffloat_low_caml(value a) {
  return(caml_copy_double(ffloat_low(Long_val(a))));
}

value ffloat_high_caml(value a) {
  return(caml_copy_double(ffloat_high(Long_val(a))));
}

value fadd_caml(value a,value b) {
  return caml_copy_double(fadd(Double_val(a), Double_val(b)));
}

value fadd_low_caml(value a,value b) {
  return caml_copy_double(fadd_low(Double_val(a), Double_val(b)));
}

value fadd_high_caml(value a,value b) {
  return caml_copy_double(fadd_high(Double_val(a), Double_val(b)));
}

value fsub_caml(value a,value b) {
  return caml_copy_double(fsub(Double_val(a), Double_val(b)));
}

value fsub_low_caml(value a,value b) {
  return caml_copy_double(fsub_low(Double_val(a), Double_val(b)));
}

value fsub_high_caml(value a,value b) {
  return caml_copy_double(fsub_high(Double_val(a), Double_val(b)));
}

value fmul_caml(value a,value b) {
  return caml_copy_double(fmul(Double_val(a), Double_val(b)));
}

value fmul_low_caml(value a,value b) {
  return caml_copy_double(fmul_low(Double_val(a), Double_val(b)));
}

value fmul_high_caml(value a,value b) {
  return caml_copy_double(fmul_high(Double_val(a), Double_val(b)));
}

value fdiv_caml(value a,value b) {
  return caml_copy_double(fdiv(Double_val(a), Double_val(b)));
}

value fdiv_low_caml(value a,value b) {
  return caml_copy_double(fdiv_low(Double_val(a), Double_val(b)));
}

value fdiv_high_caml(value a,value b) {
  return caml_copy_double(fdiv_high(Double_val(a), Double_val(b)));
}

value fprem_caml(value a,value b) {
  return caml_copy_double(fprem_l(Double_val(a), Double_val(b)));
}

value fsqrt_caml(value a) {
  return(caml_copy_double(fsqrt_l(Double_val(a))));
}

value fsqrt_low_caml(value a) {
  return(caml_copy_double(to_low(fsqrt_low_l(Double_val(a)))));
}

value fsqrt_high_caml(value a) {
  return(caml_copy_double(to_high(fsqrt_high_l(Double_val(a)))));
}

value flog_caml(value a) {
  return(caml_copy_double(flog_l(Double_val(a))));
}

value flog_low_caml(value a) {
  return(caml_copy_double(to_low(flog_low_l(Double_val(a)))));
}

value flog_high_caml(value a) {
  return(caml_copy_double(to_high(flog_high_l(Double_val(a)))));
}

value fexp_caml(value a) {
  return(caml_copy_double(fexp_l(Double_val(a))));
}

value fexp_low_caml(value a) {
  return(caml_copy_double(to_low(fexp_low_l(Double_val(a)))));
}

value fexp_high_caml(value a) {
  return(caml_copy_double(to_high(fexp_high_l(Double_val(a)))));
}

value flog_pow_caml(value a, value b) {
  return(caml_copy_double(flog_pow_l(Double_val(a), Double_val(b))));
}

value flog_pow_low_caml(value a, value b) {
  return(caml_copy_double(to_low(flog_pow_low_l(Double_val(a), Double_val(b)))));
}

value flog_pow_high_caml(value a, value b) {
  return(caml_copy_double(to_high(flog_pow_high_l(Double_val(a), Double_val(b)))));
}

value facos_caml(value a) {
  return(caml_copy_double(facos_l(Double_val(a))));
}

value facos_low_caml(value a) {
  return(caml_copy_double(to_low(facos_low_l(Double_val(a)))));
}

value facos_high_caml(value a) {
  return(caml_copy_double(to_high(facos_high_l(Double_val(a)))));
}

value fasin_caml(value a) {
  return(caml_copy_double(fasin_l(Double_val(a))));
}

value fasin_low_caml(value a) {
  return(caml_copy_double(to_low(fasin_low_l(Double_val(a)))));
}

value fasin_high_caml(value a) {
  return(caml_copy_double(to_high(fasin_high_l(Double_val(a)))));
}

value fatan_caml(value a, value b) {
  return(caml_copy_double(fatan_l(Double_val(a), Double_val(b))));
}

value fatan_low_caml(value a, value b) {
  return(caml_copy_double(to_low(fatan_low_l(Double_val(a), Double_val(b)))));
}

value fatan_high_caml(value a, value b) {
  return(caml_copy_double(to_high(fatan_high_l(Double_val(a), Double_val(b)))));
}

value fcos_caml(value a) {
  return(caml_copy_double(fcos_l(Double_val(a))));
}

value fcos_low_caml(value a) {
  return(caml_copy_double(to_low(fcos_low_l(Double_val(a)))));
}

value fcos_high_caml(value a) {
  return(caml_copy_double(to_high(fcos_high_l(Double_val(a)))));
}

value fsin_caml(value a) {
  return(caml_copy_double(fsin_l(Double_val(a))));
}

value fsin_low_caml(value a) {
  return(caml_copy_double(to_low(fsin_low_l(Double_val(a)))));
}

value fsin_high_caml(value a) {
  return(caml_copy_double(to_high(fsin_high_l(Double_val(a)))));
}

value ftan_caml(value a) {
  return(caml_copy_double(ftan_l(Double_val(a))));
}

value ftan_low_caml(value a) {
  return(caml_copy_double(to_low(ftan_low_l(Double_val(a)))));
}

value ftan_high_caml(value a) {
  return(caml_copy_double(to_high(ftan_high_l(Double_val(a)))));
}

value fcos_I_caml(value ab) {
  CAMLparam1(ab);
  CAMLlocal1(res);
  double rra, rrb;

  fcos_I(Double_field(ab, 0), Double_field(ab, 1), &rra, &rrb);
  res = caml_alloc(2 * Double_wosize, Double_array_tag);
  Store_double_field(res, 0, rra);
  Store_double_field(res, 1, rrb);
  CAMLreturn(res);
}

value fsin_I_caml(value ab) {
  CAMLparam1(ab);
  CAMLlocal1(res);
  double rra, rrb;

  fsin_I(Double_field(ab, 0), Double_field(ab, 1), &rra, &rrb);
  res = caml_alloc(2 * Double_wosize, Double_array_tag);
  Store_double_field(res, 0, rra);
  Store_double_field(res, 1, rrb);
  CAMLreturn(res);
}

value fcosh_caml(value a) {
  return(caml_copy_double(fcosh_l(Double_val(a))));
}

value fcosh_low_caml(value a) {
  return(caml_copy_double(to_low(fcosh_low_l(Double_val(a)))));
}

value fcosh_high_caml(value a) {
  return(caml_copy_double(to_high(fcosh_high_l(Double_val(a)))));
}

value fsinh_caml(value a) {
  return(caml_copy_double(fsinh_l(Double_val(a))));
}

value fsinh_low_caml(value a) {
  return(caml_copy_double(to_low(fsinh_low_l(Double_val(a)))));
}

value fsinh_high_caml(value a) {
  return(caml_copy_double(to_high(fsinh_high_l(Double_val(a)))));
}

value ftanh_caml(value a) {
  return(caml_copy_double(ftanh_l(Double_val(a))));
}

value ftanh_low_caml(value a) {
  return(caml_copy_double(to_low(ftanh_low_l(Double_val(a)))));
}

value ftanh_high_caml(value a) {
  return(caml_copy_double(to_high(ftanh_high_l(Double_val(a)))));
}

value is_neg_caml(value a) {
  return(Val_bool(signbit(Double_val(a))));
}

value fadd_I_x_caml(value ab,value x) {
  CAMLparam2(ab,x);
  CAMLlocal1(res);
  double rra, rrb;

  rra = fadd_low(Double_field(ab, 0),Double_val(x));
  rrb = fadd_high(Double_field(ab, 1),Double_val(x));

  res = caml_alloc(2 * Double_wosize, Double_array_tag);
  Store_double_field(res, 0, rra);
  Store_double_field(res, 1, rrb);
  CAMLreturn(res);
}

value fadd_I_caml(value ab,value cd) {
  CAMLparam2(ab,cd);
  CAMLlocal1(res);
  double rra, rrb;

  rra = fadd_low(Double_field(ab, 0),Double_field(cd, 0));
  rrb = fadd_high(Double_field(ab, 1),Double_field(cd, 1));

  res = caml_alloc(2 * Double_wosize, Double_array_tag);
  Store_double_field(res, 0, rra);
  Store_double_field(res, 1, rrb);
  CAMLreturn(res);
}

value fsub_I_x_caml(value ab,value x) {
  CAMLparam2(ab,x);
  CAMLlocal1(res);
  double rra, rrb;

  rra = fsub_low(Double_field(ab, 0),Double_val(x));
  rrb = fsub_high(Double_field(ab, 1),Double_val(x));

  res = caml_alloc(2 * Double_wosize, Double_array_tag);
  Store_double_field(res, 0, rra);
  Store_double_field(res, 1, rrb);
  CAMLreturn(res);
}

value fsub_x_I_caml(value x,value ab) {
  CAMLparam2(x,ab);
  CAMLlocal1(res);
  double rra, rrb;

  rra = fsub_low(Double_val(x),Double_field(ab, 1));
  rrb = fsub_high(Double_val(x),Double_field(ab, 0));

  res = caml_alloc(2 * Double_wosize, Double_array_tag);
  Store_double_field(res, 0, rra);
  Store_double_field(res, 1, rrb);
  CAMLreturn(res);
}

value fsub_I_caml(value ab,value cd) {
  CAMLparam2(ab,cd);
  CAMLlocal1(res);
  double rra, rrb;

  rra = fsub_low(Double_field(ab, 0),Double_field(cd, 1));
  rrb = fsub_high(Double_field(ab, 1),Double_field(cd, 0));

  res = caml_alloc(2 * Double_wosize, Double_array_tag);
  Store_double_field(res, 0, rra);
  Store_double_field(res, 1, rrb);
  CAMLreturn(res);
}

