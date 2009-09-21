/* AMPL model for the Kepler conjecture
File created Sep 19 2009
Thomas C. Hales

The model considers the set of blades around a spine.

The set ITRIANGLE is the index set for the triangles.
QUARTER index set for quarters.
CELL4 non quarter 4-cells.
CELL23 2&3 cell combinations.

*/

# data provides the following.
param caseID;
param CFACE;
param CBLADE 'number of blades' >= 2, <= 4; 

# constants.
param pi := 3.1415926535897932;
param lb := -0.00569;  # quarter lower bound.

# indexing sets
set IFACE := 0..(CFACE -1);
set EFACE 'extended dart' within IFACE cross IFACE cross IFACE;
set BLADE 'blades" within IFACE cross IFACE;

# basic variables
var azim{FACE} >= 0, <= 2*pi;
var tau{FACE} >= -1, <= 4*
var y1 >= 2.52, <=2.52;
var y2{FACE} >=2, <=sqrt8;
var y3{FACE} >=2, <=sqrt8;
var y4{FACE} >=2 <=sqrt8;
var y5{FACE} >=2, <=sqrt8;
var y6{FACE} >=2, <=sqrt8;

#report variables
var tausum;

## objective
minimize objective:  tausum;

## equality constraints
tau_sum: sum {i in FACE} tau[i] = tausum;
azim_sum:  sum {i in FACE} azim[i] = 2.0*pi;
y1_def{(i3,i1,i2,j) in EFACE}: y1[i1,j] = yn[i1];
y2_def{(i3,i1,i2,j) in EFACE}: y2[i1,j] = yn[i2];
y3_def{(i3,i1,i2,j) in EFACE}: y3[i1,j] = yn[i3];
y4_def{(i3,i1,i2,j) in EFACE :  (i1,j) in APEX3}: y4[i1,j] = ye[i2,j];
y5_def{(i3,i1,i2,j) in EFACE}: y5[i1,j] = ye[i3,j];
y6_def{(i3,i1,i2,j) in EFACE}: y6[i1,j] = ye[i1,j];

## inequality constraints

solve;
display caseID;
display tausum;
