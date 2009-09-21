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

# data supplied indexing sets
set IFACE := 0..(CFACE -1);
set BLADE 'blades" within IFACE cross IFACE; # adjacent ordered pairs of faces, cyclic order.
set SMALLBLADE within BLADE;
set BIGBLADE within BLADE;
set EFACE := {(i1,i2,i3) in IFACE cross IFACE cross IFACE : 
   (i1,i2) in BLADE and
   (i2,i3) in BLADE};

set QUARTER within setof {(i1,i2,i3) in EFACE : (i1,i2) in SMALLBLADE and (i2,i3) in SMALLBLADE} i2;

#more branching sets.
set POSGAMMA within IFACE;  # gamma < 0.
set FOURCELLNQ within NONQUARTER;  # excludes quarters!
set WT1 within IFACE;
set DIH23 within WT1; #gamma4L, dih > 2.3.

set NONQUARTER:= IFACE DIFF QUARTER;
set TWO3CELL := NONQUARTER DIFF FOURCELL;

#


# basic variables
# gamma = gamma4Lbwt on 4-cell, = gamma23Lwb on 2&3-cell.
var azim{FACE} >= 0, <= 2*pi;
var gamma{FACE} >= -1, <= 0.1;
var gamma3_126{TWO3CELL} >= 0, <= 0.1;  #lower bound in 4869905472
var gamma3_135{TWO3CELL} >= 0, <= 0.1;
var gamma2{TWO3CELL} >= 0, <= 0.1;

var y1 >= 2 * 1.2317544220903185, <=2.6508; #critical edge
var y2{FACE} >=2, <=sqrt8;
var y3{FACE} >=2, <=sqrt8;
var y4{FACE} >=2 <=sqrt8;
var y5{FACE} >=2, <=sqrt8;
var y6{FACE} >=2, <=sqrt8;

#report variables
var gammasum;

## objective
minimize objective:  gammasum;

## equality constraints
gamma_sum: sum {i in FACE} gamma[i] = gammasum;
azim_sum:  sum {i in FACE} azim[i] = 2.0*pi;
y2y3{(i1,i2) in BLADE}: y3[i1] = y2[i2];
y5y6{(i1,i2) in BLADE}: y5[i1]=  y6[i2];
gamma23{i in TWO3CELL}: gamma2[i]+gamma3_126[i]+gamma3_135[i]=gamma[i];

## computer generated inequality constraints
gammapos{i in NONQUARTER}: gamma[i] >= 0; #2477215213, #8328676778
quarter_23{(i,j) in BLADE : i in QUARTER, j in TWO3CELL} : gamma[i] + gamma3_126[j] >= 0; #118115412
quarter_23{(i,j) in BLADE : j in QUARTER, i in TWO3CELL} : gamma[j] + gamma3_135[i] >= 0; #118115412
quarterneg{i in QUARTER DIFF POSGAMMA} : gamma[i] <= 0;
quarterpos{i in QUARTER inter POSGAMMA} : gamma[i] >=0;
quarternegdih{i in QUARTER DIFF POSGAMMA}: azim[i] <= 1.65;  #2300537674
fourcellazim{i in FOURCELL union QUARTER}: azim[i] <= 2.8; #6652007036
wtunder1{i in IFACE DIFF WT1}: azim[i] <= 2.3; #1738910218, #7080972881.
gammaquarter{i in QUARTER}: gamma[i] >= -0.00569; #9455898160.
gammadih23{i in DIH23}: gamma[i] >= 0.0057; #7274157868

azim1 '5653753305' {i in QUARTER}: gamma[i] + 0.0659 - azim[i]*0.042 >= 0; 
azim2 '9939613598' {i in WT1 inter NONQUARTER}: gamma[i] - 0.00457511 - 0.00609451*azim[i] >= 0;



solve;
display caseID;
display gammasum;
