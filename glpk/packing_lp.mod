/* ========================================================================== */
/* FLYSPECK - GLPK                                              */
/*                                                                            */
/* Linear Programming, AMPL format (non-formal)    */
/* Chapter: Packing                                                     */
/* Author: Thomas C. Hales                                                    */
/* Date: 2009-09-19                                                           */
/* ========================================================================== */


/* 

The model considers the set of blades around a spine.

QU index set for quarters.
QX non quarter 4-cells.
QY 2&3 cell combinations.

*/

# data provides the following.
param CBLADE 'number of blades' >= 2, <= 4; 

# constants.
param pi := 3.1415926535897932;
param hmin:= 1.2317544220903185;
param h0:= 1.26;
param hmax:= 1.3254;
param sqrt2:= 1.4142135623730951;
param lb := -0.00569;  # quarter lower bound.

# data supplied indexing sets
set FACE := 0..(CBLADE -1);
#set BLADE within FACE cross FACE; # adjacent ordered pairs of faces, cyclic order.
set BLADE := {(i,j) in  FACE cross FACE : 0 = (i + 1 +CBLADE -j) mod CBLADE  }; # adjacent  pairs
set EFACE := {(i1,i2,i3) in FACE cross FACE cross FACE : 
   (i1,i2) in BLADE and
   (i2,i3) in BLADE};


# data supplied branching sets.  
#There is the "unbranched" state, branching in direction "X", branching in direction "not-X"
# SBLADE/NONSBLADE, branch on blades.
# QU/QX/QY : QUARTER,NONQUARTER-4CELL,23-CELL. 
# QXD,NONQXD: branch on QX.
# NEGQU/POSQU branch on QU
# HALFWT/FULLWT branch on QX inter HASSMALL.

set SBLADERAW within FACE;  #non-spine edges are between 2 and 2*hmin.
set NONSBLADERAW within  FACE diff SBLADERAW;
set SBLADE := {(i,j) in BLADE : j in SBLADERAW};
set NONSBLADE := {(i,j) in BLADE : j in NONSBLADERAW};
set HASSMALL := setof {(i1,i2,i3) in EFACE : (i1,i2) in SBLADE and (i2,i3) in SBLADE} i2;
set QU within HASSMALL;
set QX within FACE diff QU; 
set QY within FACE diff (QX union QU);
set NEGQU within QU; #precisely the set of quarters where gamma<0.
set POSQU within QU; 
set QXD within QX;  # those with dih > 2.3.
set NONQXD within QX diff QXD;
set HALFWT within HASSMALL inter QX; # those QX with y1,y4 critical and HASSMALL blades
set FULLWT within (HASSMALL inter QX) diff HALFWT;  #those QX with y4>= 2*hmax and HASSMALL blades.

#
set ONESMALLa := setof {(i1,i2,i3) in EFACE : (i1,i2) in SBLADE and (i2,i3) in NONSBLADE} i2;
set ONESMALLb := setof {(i1,i2,i3) in EFACE : (i1,i2) in NONSBLADE and (i2,i3) in SBLADE} i2;
set I10 := {(i,j) in BLADE : i in (QX inter HASSMALL) and j in QY};
set I11 := {(i,j) in BLADE : j in (QX inter HASSMALL) and i in QY};


# basic variables
# gamma = gamma4Lbwt on 4-cell, = gamma23Lwtb on 2&3-cell.
var azim{FACE} >= 0, <= 2*pi;
var gamma{FACE} >= lb, <= 0.1;
var gamma3a{QY} >= 0, <= 0.1;  #lower bound in ID[4869905472]
var gamma3b{QY} >= 0, <= 0.1;
var gamma2{QY} >= 0, <= 0.1;

var y1 >= 2 * hmin, <= 2*hmax ; #critical edge
var y2{FACE} >=2, <= 2*sqrt2;
var y3{FACE} >=2, <=2*sqrt2;
var y4{i in QU union QX} >=2, <= 2*sqrt2; 
var y5{FACE} >=2, <=2*sqrt2;
var y6{FACE} >=2, <=2*sqrt2;

#report variables
var gammasum;

## objective
minimize objective:  gammasum;

## equality constraints
gamma_sum: sum {i in FACE} gamma[i] = gammasum;
azim_sum:  sum {i in FACE} azim[i] = 2.0*pi;
y2y3{(i1,i2) in BLADE}: y3[i1] = y2[i2];
y5y6{(i1,i2) in BLADE}: y5[i1]=  y6[i2];
gamma23{i in QY}: gamma2[i]+gamma3a[i]+gamma3b[i]=gamma[i];


##inequalities by definition of branch.
y3small {(i,j) in SBLADE}: y3[i] <= 2*hmin;
y5small {(i,j) in SBLADE}: y5[i] <= 2*hmin;
y35big {(i,j) in NONSBLADE} : y3[i]+y5[i] >= 2*hmin + 2;
y4qu {i in QU} : y4[i] <= 2*hmin;
qxd_azim{i in QXD}: azim[i] >= 2.3;
nqxd_azim{i in NONQXD}: azim[i] <= 2.3;
negqu {i in NEGQU} : gamma[i] <= 0;
posqu{i in POSQU} : gamma[i] >=0;
halfwt{i in HALFWT}:  y4[i] >= 2*hmin;
halfwtup{i in HALFWT}: y4[i] <= 2*hmax;
fullwt{i in FULLWT}: y4[i] >= 2*hmax;


## computer generated inequality constraints
#1,2,3 blades
gammapos{i in QX}: gamma[i] >= 0; #ID[2477215213], ID[8328676778], 
quarter3a{(i,j) in BLADE : i in QU and j in QY} : gamma[i] + gamma3a[j] >= 0; #ID[118115412]
quarter3b{(i,j) in BLADE : j in QU and i in QY} : gamma[j] + gamma3b[i] >= 0; #ID[118115412]
quarternegdih{i in NEGQU}: azim[i] <= 1.65;  #ID[2300537674]
fourcellazim{i in QU union QX}: azim[i] <= 2.8; #ID[6652007036]
wtunder1{i in QXD}:  gamma[i] >= 0.0057;  #ID[7274157868] (wt1)  cf.  ID[7080972881], ID[1738910218] (reduce to wt1)
gammaquarter 'ID[9455898160]' {i in QU}: gamma[i] >= -0.00569; 

#4blades
azim1 '5653753305' {i in QU}: gamma[i] + 0.0659 - azim[i]*0.042 >= 0; 
azim2 '9939613598' {i in FULLWT}: gamma[i] - 0.00457511 - 0.00609451*azim[i] >= 0;
azim3 '4003532128' {i in QY} : gamma[i] - 0.00457511 - 0.00609451 * azim[i] >= 0;
azim4 '6206775865' {i in QU}: gamma[i] + 0.0142852 - 0.00609451 * azim[i] >= 0;
azim5 '5814748276' {i in QU}: gamma[i] - 0.00127562 + 0.00522841 * azim[i] >= 0;
azim6 '3848804089' {i in QU}: gamma[i] - 0.161517 + 0.119482* azim[i] >= 0;
##skip ID[1821661595], ID[7907792228],  for 5 blades, done in text.
azim7 'ID[3803737830]' {i in QX}: gamma[i] - 0.0105256 + 0.00522841*azim[i] >= 0;
azim8 'ID[9063653052]' {i in (ONESMALLa union ONESMALLb) inter QX}: gamma[i] >= 0.0057; 
azim9 'ID[2134082733]' {i in HASSMALL inter QX}: gamma[i] - 0.213849 + 0.119482*azim[i] >= 0;
ineq10 'ID[5400790175a]' {(i,j) in I10}: gamma[i]+gamma3a[j] >= 0.0057;
ineq11 'ID[5400790175b]' {(i,j) in I11}:  gamma[j]+gamma3b[i] >= 0.0057;

solve;
display gammasum;
