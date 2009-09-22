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
param hmin:= 1.2317544220903185;
param h0:= 1.26;
param hmax:= 1.3254;
param sqrt2:= 1.4142135623730951;
param lb := -0.00569;  # quarter lower bound.

# data supplied indexing sets
set IFACE := 0..(CFACE -1);
set BLADE 'blades" within IFACE cross IFACE; # adjacent ordered pairs of faces, cyclic order.
set EFACE := {(i1,i2,i3) in IFACE cross IFACE cross IFACE : 
   (i1,i2) in BLADE and
   (i2,i3) in BLADE};


#data supplied branching sets: 
# SBLADE/NONSBLADE, branch on blades.
# QUARTER/NONQUARTER, branch on IFACE,
# NEGQUARTER/POSQUARTER branch on QUARTER
# CELL4/NONCELL4 branch on IFACE
# CELL4D/NONCELL4D branch on CELL4;

set SBLADE within BLADE;  #non-spine edges are between 2 and 2*hmin.
set NONSBLADE within  BLADE diff SBLADE;;
set QUARTER within setof {(i1,i2,i3) in EFACE : (i1,i2) in SBLADE and (i2,i3) in SBLADE} i2;
set NONQUARTER within IFACE DIFF QUARTER;
set NEGQUARTER within QUARTER; #precisely the set of quarters where gamma<0.
set POSQUARTER within QUARTER; 
set CELL4; #all 4-cells.
set NONCELL4 within IFACE diff CELL4;
set CELL4D within CELL4;  # those with dih > 2.3.
set NONCELL4D := within CELL4 diff CELL4D;




#


# basic variables
# gamma = gamma4Lbwt on 4-cell, = gamma23Lwb on 2&3-cell.
var azim{FACE} >= 0, <= 2*pi;
var gamma{FACE} >= -1, <= 0.1;
var gamma3a{NONCELL4} >= 0, <= 0.1;  #lower bound in 4869905472
var gamma3b{NONCELL4} >= 0, <= 0.1;
var gamma2{NONCELL4} >= 0, <= 0.1;

var y1 >= 2 * hmin, <= 2*hmax ; #critical edge
var y2{FACE} >=2, <= 2*sqrt2;
var y3{FACE} >=2, <=2*sqrt2;
var y4{FACE} >=2 <= 6;
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
gamma23{i in NONCELL4}: gamma2[i]+gamma3a[i]+gamma3b[i]=gamma[i];

##inequalities by definition
y3small {(i,j) in SBLADE}: y3[i] <= 2*hmin;
y5small {(i,j) in SBLADE}: y5[i] <= 2*hmin;
y35big {(i,j) in NONSBLADE} : y3[i]+y5[i] >= 2*hmin + 2;
y4quarter {i in QUARTER} : y4 <= 2*hmin;
gammaneg {i in NEGQUARTER} : gamma[i] <= 0;
quarterpos{i in IFACE diff NEGQUARTER} : gamma[i] >=0;
y4cell4 {i in CELL4}: y4 <= 2*sqrt8;
cell4d{i in CELL4D}: azim[i] >= 2.3;
cell4dx{i in CELL4 diff CELL4D}: azim[i] <= 2.3;




## computer generated inequality constraints
#1,2,3 blades
gammapos{i in NONQUARTER}: gamma[i] >= 0; #2477215213, #8328676778, 
quarter_23{(i,j) in BLADE : i in QUARTER and j in NONCELL4} : gamma[i] + gamma3a[j] >= 0; #118115412
quarter_23{(i,j) in BLADE : j in QUARTER and i in NONCELL4} : gamma[j] + gamma3b[i] >= 0; #118115412
quarternegdih{i in NEGQUARTER}: azim[i] <= 1.65;  #2300537674
fourcellazim{i in CELL4}: azim[i] <= 2.8; #6652007036
wtunder1{i in CELL4D}:  gamma[i] >= 0.0057;   #7274157868   cf.  #7080972881, #1738910218.
gammaquarter{i in QUARTER}: gamma[i] >= -0.00569; #9455898160.

#4blades
azim1 '5653753305' {i in QUARTER}: gamma[i] + 0.0659 - azim[i]*0.042 >= 0; 

set WT1NQ := setof {(i1,i2,i3) in EFACE : (i1,i2) in SBLADE and (i2,i3) in SBLADES and i2 in CELL4 and i2 in NONQUARTER} (i2) ;  # y4>= 2*hmax.
y4wt1 {i in WT1NQ}: y4 >= 2*hmax;
azim2 '9939613598' {i in WT1NQ}: gamma[i] - 0.00457511 - 0.00609451*azim[i] >= 0;

azim3 '4003532128' {i in NONCELL4} : gamma[i] - 0.00457611 - 0.00609451 * azim[i] >= 0;
azim4 '6206775865' {i in QUARTER}: gamma[i] + 0.0142852 - 0.00609451 * azim[i] >= 0;
azim5 '5814748276' {i in QUARTER}: gamma[i] - 0.00127562 + 0.00522841 * azim[i] >= 0;
azim6 '3848804089' {i in QUARTER}: gamma[i] - 0.161517 + 0.119482* azim[i] >= 0;
#skip 1821661595, 7907792228,  for 5 blades.

XXD THESE THREE 7,8,9
azim7 '3803737830' {}: gamma[i] - 0.0105256 + 0.00522841*azim[i] >= 0;
azim8 '9063653052' {}: gamma[i] > 0.0057; 
azim9 '2134082733' {}: gamma[i] - 0.213849 + 0.119482*azim[i] >= 0;

set I10 := {(i,j) in BLADE : i in CELL4 and i in NONQUARTER and j NONCELL4};
ineq10 '5400790175a' {(i,j) in I10};  gamma[i]+gamma3a[j] >= 0.0057;
set I11 := {(i,j) in BLADE : j in CELL4 and j in NONQUARTER and i NONCELL4};
ineq10 '5400790175b' {(i,j) in I11};  gamma[j]+gamma3b[i] >= 0.0057;



solve;
display caseID;
display gammasum;
