/* ========================================================================== */
/* FLYSPECK - GLPK                                              */
/*                                                                            */
/* Linear Programming, AMPL format (non-formal)    */
/* Chapter: Tame Hypermap                 */
/* Lemma: KCBLRQC (Tame Table B) */
/* Author: Thomas C. Hales                                                    */
/* Date: 2010-06-14                   */
/* ========================================================================== */


/* 

The model considers nodes of type (p,q,0) and computes
the tame table constants b(p,q) and a(5,0,1).

*/

# data provides the following.
param p 'number of triangles' >= 0, <= 10; 
param q 'number of quads' >= 0, <= 10; 
param r 'number of exceptional' >= 0, <= 1;

# constants.
param pi := 3.1415926535897932;

# basic variables
var azimp  >= 0.852, <= 1.9;  #5735387903, 5490182221
var azimq >= 1.15, <= pi; #2570626711, convexity
var azimr >= 1.15, <= pi; 
var taup >=0;
var tauq >= 0.206;  # tameTableD[4,0].


#report variables
var tausum;

## objective
minimize objective:  tausum;

## equality constraints
anglesum: p* azimp + q * azimq + r * azimr = 2.0 * pi;
tausumdef: p*taup + q*tauq = tausum;  # exclude exceptionals.

## nonlinear inequality constraints

p1 'ID[3296257235]' : 
 taup  + 0.626 * azimp - 0.77 >= 0.0;
p2 'ID[8519146937]' :
 taup  -  0.259 * azimp + 0.32 >= 0.0;
p3 'ID[4667071578]' :
  taup  -  0.507 * azimp + 0.724 >= 0.0;

q1 'ID[7043724150]' :
 tauq  + 4.72 * azimq - 6.248 >= 0.0;
q2 'ID[6944699408]' :
 tauq  + 0.972 * azimq -  1.707 >= 0.0;
q3 'ID[4240815464]' :
 tauq  + 0.7573 *azimq - 1.433 >= 0.0;
q4 'ID[3862621143]' :
 tauq  - 0.453 * azimq +  0.777 >= 0.0;

solve;
display tausum;
