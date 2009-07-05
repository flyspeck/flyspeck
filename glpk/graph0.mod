/* AMPL model for the Kepler conjecture
File created May 8, 2009
Revised June 20, 2009
Thomas C. Hales

The model starts with a tame hypermap, then breaks certain quadrilaterals into two flats, certain pentagons into a flat+big4face or into 2 flats+apiece, certain hexagons into flat+big5face.  The new internal edges have length 2.52--sqrt8.


The sets ITRIANGLE, IQUAD, IPENT, IHEX index the remaining standard regions.  The other faces are subregions obtained by subdividing a standard region as just described.  If a standard region is known to contain no flat quarters, then it belongs to SUPER8.

****************

The branching has have following types.
* 2-way split on a triangular standard region according to y4+y5+y6 <= 6.25.
* 2-way  split on a node according to yn <= 2.18
* 3-way split on a standard quad, according to SUPER8, flats one way, flats the other way.
* 11-way split on std. pent, SUPER8, 5 (flat+big4face), 5 (flat+flat+Apiece).
* 6-way split on std. hex, SUPER8, 6 (flat+big5face).
Note that a big5face may have other flats within it, that are not used in branching.  This is done to keep the branching on hexagons to a minimum.

****************

Sets provided in the data file :
hypermapID: a numerical identifier of the case.
CVERTEX: the number of vertices. 
CFACE: the number of faces.  Standard regions that have been subdivided are not counted.
EDART: quadruples (i1,i2,i3,j) where (i1,j) is a dart such that f(i1,j) = (i2,j), f(i2,j)=(i3,j).
ITRIANGLE, IQUAD, IPENT, IHEX: remaining standard faces with 3,4,5,6 darts.
SUPER8: quads, pents, and hexes that are known not to have any flat quarters.
FLAT: the apex darts of flat quarters.  It is the dart opposite the long edge.
APIECE: the apex darts of flat quarters.
BIG5APEX: apex dart of complement of flat in hex, where the apex dart is defined as 
  in the BIG4APEX.  It is *not* the dart opposite the long edge.
BIG4APEX: apex dart in complement of flat in pent, where the apex dart is defined as
  the dart x s.t. f x and f^2 x are the two darts along the long edge.
BIGTRI: standard triangles with y4+y5+y6>=6.25;
SMALLTRI: standard triangles with y4+y5+y6<=6.25;
HIGHVERTEX: vertex with yn >= 2.18;
LOWVERTEX: vertex with yn <= 2.18;

*/

param hypermapID;
param pi := 3.1415926535897932;
param delta0 := 0.5512855984325308;
param tgt := 1.54065864570856;
param sqrt8 := 2.8284271247461900;

param CVERTEX 'number of vertices' >= 13, <= 14; 
param CFACE 'number of faces' >= 0; 


# directed edge (i,j) identified with tail of arrow.
set IVERTEX := 0..(CVERTEX-1);
set FACE := 0..(CFACE-1);
set EDART 'extended dart' within IVERTEX cross IVERTEX cross IVERTEX cross FACE;
set DART := setof {(i1,i2,i3,j) in EDART} (i1,j);
set DEDGE := DART;
set EDGE within DART cross DART := setof{(i1,i2,i3,j1) in EDART,(i0,i3,i2,j2) in EDART}(i2,j1,i3,j2);

set ITRIANGLE; 
set IQUAD;  
set IPENT; 
set IHEX; 
set STANDARDR := ITRIANGLE union IQUAD union IPENT union IHEX; # standard regions.
set DART3:= {(i,j) in DART: j in ITRIANGLE};
set DART4:= {(i,j) in DART: j in IQUAD};

# branch sets
set SUPER8 within IQUAD union IPENT union IHEX;
set SUBREGION := FACE diff STANDARDR;
set FLAT within {(i,j) in DART : j in SUBREGION};
set APIECE within {(i,j) in DART : j in SUBREGION};

# APEX3 does not include all darts of FLAT and APIECE, only the distinguished one.
set APEX3 := FLAT union APIECE union {(i,j) in DART: j in ITRIANGLE};
set BIG5APEX within {(i,j) in DART : j in SUBREGION};  
set BIG4APEX within {(i,j) in DART: j in SUBREGION};  
set BIGTRI within ITRIANGLE;
set SMALLTRI within ITRIANGLE;
set HIGHVERTEX within IVERTEX;
set LOWVERTEX within IVERTEX;

## SPECIAL SETS OF DARTS ##

# darts with opposite at least 2.52 others in [2,2.52].
set DARTX :=  BIG5APEX union
   setof{(i1,i2,i3,j) in EDART: (i3,j) in BIG5APEX}(i1,j) union
   setof{(i1,i2,i3,j) in EDART: (i3,j) in BIG5APEX}(i2,j) union
   {(i,j) in DART: j in IQUAD union IPENT union IHEX};

# darts with opposite at least s8, others in [2,2.52].
set DARTZ := {(i,j) in DART: j in SUPER8} union BIG4APEX union
    setof{(i1,i2,i3,j) in EDART : (i2,j) in BIG4APEX}(i1,j);


# basic variables
var azim{DART} >= 0, <= pi;
var ln{IVERTEX} >= 0, <= 1;
var rhazim{DART} >=0, <= pi + delta0;
var yn{IVERTEX} >= 2, <= 2.52;
var ye{DEDGE} >= 2, <= 2.52;
var rho{IVERTEX} >= 1, <= 1 + delta0/pi;
var sol{FACE} >= 0, <= 4.0*pi;
var tau{FACE} >= 0, <= tgt;
var y1{DART} >= 0, <=2.52;
var y2{DART} >=0, <=2.52;
var y3{DART} >=0, <=2.52;
var y4{APEX3} >=0, <=sqrt8;
var y5{DEDGE} >=0, <=sqrt8;
var y6{DEDGE} >=0, <=sqrt8;


#report variables
var lnsum;
var ynsum;


## objective
maximize objective:  lnsum;

## equality constraints
lnsum_def: sum{i in IVERTEX} ln[i]  = lnsum;
ynsum_def: sum{i in IVERTEX} yn[i] = ynsum;
azim_sum{i in IVERTEX}:  sum {(i,j) in DART} azim[i,j] = 2.0*pi;
rhazim_sum{i in IVERTEX}:  sum {(i,j) in DART} rhazim[i,j] = 2.0*pi*rho[i];
sol_sum{j in FACE}: sum{(i,j) in DART} (azim[i,j] - pi) = sol[j] - 2.0*pi;
tau_sum{j in FACE}: sum{(i,j) in DART} (rhazim[i,j] - pi -delta0) = tau[j] - 2.0*(pi+delta0);
ln_def{i in IVERTEX}: ln[i] = (2.52 - yn[i])/0.52;
rho_def{i in IVERTEX}: rho[i] = (1 + delta0/pi) - ln[i] * delta0/pi;
edge{(i1,j1,i2,j2) in EDGE}: ye[i1,j1] = ye[i2,j2];
y1_def{(i3,i1,i2,j) in EDART}: y1[i1,j] = yn[i1];
y2_def{(i3,i1,i2,j) in EDART}: y2[i1,j] = yn[i2];
y3_def{(i3,i1,i2,j) in EDART}: y3[i1,j] = yn[i3];
y4_def{(i3,i1,i2,j) in EDART :  (i1,j) in APEX3}: y4[i1,j] = ye[i2,j];
y5_def{(i3,i1,i2,j) in EDART}: y5[i1,j] = ye[i3,j];
y6_def{(i3,i1,i2,j) in EDART}: y6[i1,j] = ye[i1,j];

## inequality constraints
main: sum{i in IVERTEX} ln[i] >= 12;
RHA{(i,j) in DART}: azim[i,j] <= rhazim[i,j];
RHB{(i,j) in DART}: rhazim[i,j] <= azim[i,j]*(1+delta0/pi);

## branch definitional inequalities
ybig{(i,j) in DART3 : j in SMALLTRI}: 
  y4[i,j]+y5[i,j]+y6[i,j] >= 6.25;
ysmall{(i,j) in DART3 : j in SMALLTRI}: 
  y4[i,j]+y5[i,j]+y6[i,j] <= 6.25;
yhigh{i in HIGHVERTEX}: yn[i] >= 2.18;
ylow{i in LOWVERTEX}: yn[i] <= 2.18;

# The corresponding bounds on APIECE, BIGAPEX4, BIGAPEX5 are redundant:
y4_bound{(i,j) in DART3}: y4[i,j] <= 2.52;
y5_bound{(i,j) in DART3}: y5[i,j] <= 2.52;
y6_bound{(i,j) in DART3}: y6[i,j] <= 2.52;
y4_boundF{(i,j) in FLAT}: y4[i,j] >= 2.52;
y5_boundF{(i,j) in FLAT}: y5[i,j] <= 2.52;
y6_boundF{(i,j) in FLAT}: y6[i,j] <= 2.52;

# tau inequality (Main Estimate)

tau3{j in ITRIANGLE}: tau[j] >= 0;
tau4{j in IQUAD}: tau[j] >= 0.206;
tau5{j in IPENT}: tau[j] >= 0.483;
tau6{j in IHEX}: tau[j] >= 0.76;

## interval arithmetic bounds DART3 ##

azmin 'ID[5735387903]' {(i,j) in DART3} : azim[i,j] >= 0.852;

azmax 'ID[5490182221]' {(i,j) in DART3}: azim[i,j] <= 1.893;

tau_azim3A 'ID[3296257235]' {(i,j) in DART3}: 
  tau[j]+0.626*azim[i,j] - 0.77 >= 0;

tau_azim3B 'ID[8519146937]' {(i,j) in DART3}: 
  tau[j]-0.259*azim[i,j] + 0.32 >= 0;

tau_azim3C 'ID[4667071578]' {(i,j) in DART3}: 
  tau[j]-0.507*azim[i,j] + 0.724 >= 0;

tau_azim3D 'ID[1395142356]' {(i,j) in DART3}: 
  tau[j] + 0.001 -0.18*(y1[i,j]+y2[i,j]+y3[i,j]-6) - 0.125*(y4[i,j]+y5[i,j]+y6[i,j]-6) >= 0;

solyA 'ID[7394240696]' {(i,j) in DART3}: 
  sol[j] - 0.55125 - 0.196*(y4[i,j]+y5[i,j]+y6[i,j]-6) + 0.38*(y1[i,j]+y2[i,j]+y3[i,j]-6) >= 0;

solyB 'ID[7726998381]' {(i,j) in DART3}: 
  -sol[j] + 0.5513 + 0.3232*(y4[i,j]+y5[i,j]+y6[i,j]-6) - 0.151*(y1[i,j]+y2[i,j]+y3[i,j]-6) >= 0;

azminA 'ID[4047599236]'  {(i,j) in DART3}: azim[i,j] - 1.2308 
  + 0.3639*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.235*(y1[i,j]-2) - 0.685*(y4[i,j]-2) >= 0;

azmaxA 'ID[3526497018]' {(i,j) in DART3}: -azim[i,j] + 1.231 
  - 0.152*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) + 0.5*(y1[i,j]-2) + 0.773*(y4[i,j]-2) >= 0;


rhazminA 'ID[5957966880]' {(i,j) in DART3}: rhazim[i,j] - 1.2308 
  + 0.3639*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.6*(y1[i,j]-2) - 0.685*(y4[i,j]-2) >= 0;



## interval arithmetic bounds DART4 ##

tau_azim4A 'ID[7043724150]' {(i,j) in DART4}:
  tau[j] + 4.72*azim[i,j] - 6.248 >= 0;

tau_azim4B 'ID[6944699408]' {(i,j) in DART4}:
  tau[j] + 0.972*azim[i,j] - 1.707 >= 0;

tau_azim4C 'ID[4240815464]' {(i,j) in DART4}:
  tau[j] + 0.7573*azim[i,j] - 1.4333 >= 0;

tau_azim4D 'ID[3862621143]' {(i,j) in DART4}:
  tau[j] + 0.453*azim[i,j] + 0.777 >= 0;

## MAIN ESTIMATE SUPER8 BIG4 BIG5 ##

tau3h {(i,j) in FLAT}: tau[j] >= 0.103;
tauAh {(i,j) in APIECE}: tau[j] >= 0.277;
tauB4h {(i,j) in BIG4APEX}: tau[j] >= 0.492;
tauB5h {(i,j) in BIG5APEX}: tau[j] >= 0.657;
tau4h{j in IQUAD inter SUPER8}: tau[j] >= 0.256;
tau5h{j in IPENT inter SUPER8}: tau[j] >= 0.751;
tau6h{j in IHEX inter SUPER8}: tau[j] >= 0.91;


## more interval arithmetic on nonstandard triangles  ##

azminX 'ID[3020140039]' {(i,j) in DARTX}: 
  azim[i,j] - 1.629  + 0.402*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.315*(y1[i,j]-2)  >= 0;

azminZ 'ID[9414951439]' {(i,j) in DARTZ}:
  azim[i,j] - 1.91 + 0.458 * (y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.342*(y1[i,j]-2) >= 0;


#branch FLAT inequality

flattau 'ID[8248508703]' {(i,j) in FLAT}:
  tau[j] - 0.1 - 0.265*(y5[i,j]+y6[i,j]-4) - 0.06*(y4[i,j]-2.52) 
   - 0.16*(y1[i,j]-2) -  0.115*(y2[i,j]+y3[i,j]-4) >=0;

flatazim 'ID[3318775219]' {(i,j) in FLAT}:
  azim[i,j] - 1.629 + 0.414*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8)
-0.763*(y4[i,j]-2.52) - 0.315*(y1[i,j]-2) >= 0;

flatazimmax 'ID[9922699028]' {(i,j) in FLAT}:
  -azim[i,j] + 1.6294 - 0.2213*(y2[i,j]+y3[i,j]+y5[i,j]-y6[i,j]-8)
  +0.913*(y4[i,j]-2.52) + 0.728*(y1[i,j]-2) >= 0;

flatazim2 'ID[5000076558]' {(i1,i,i3,j) in EDART : (i,j) in FLAT}:
  azim[i3,j] - 1.083 + 0.6365*(y1[i,j]-2) - 0.198*(y2[i,j]-2)
  +0.352*(y3[i,j]-2) + 0.416*(y4[i,j]-2.52)
  -0.66*(y5[i,j]-2) + 0.071*(y6[i,j]-2) >= 0;

flatrhazim 'ID[9251360200]' {(i,j) in FLAT}:
  rhazim[i,j]
  -1.629 - 0.866*(y1[i,j]-2) + 0.3805*(y2[i,j]+y3[i,j]-4)
  -0.841*(y4[i,j]-2.52) + 0.501*(y5[i,j]+y6[i,j]-4) >= 0;

flatrhazim2 'ID[9756015945]' {(i1,i,i3,j) in EDART: (i,j) in FLAT}:
  rhazim[i3,j] -1.08
  +0.6362*(y1[i,j]-2) -0.565*(y2[i,j]-2)+0.359*(y3[i,j]-2)
  +0.416*(y4[i,j]-2.52) -0.666*(y5[i,j]-2) +0.061*(y6[i,j]-2) >=0;

#branch APIECE-BIGPIECE inequality
#We get six inequalities from a single non-linear inequality,
#  depending on the constraints on y4, and symmetries.

# darts with y4>= 2.52, y6 [2.52,s8], others [2,2.52]
big5azim46 'ID[1812128999]' {(i1,i,i3,j) in EDART: (i1,j) in BIG5APEX}: 
  azim[i,j]  - 1.448
  -0.266*(y1[i,j]-2) + 0.295*(y2[i,j]-2) + 0.57*(y3[i,j]-2)
   -0.745*(2.52-2.52)   + 0.268*(y5[i,j]-2) + 0.385*(y6[i,j]-2.52) >= 0;

big4azim46 'ID[1812128999]' {(i1,i,i3,j) in EDART: (i1,j) in BIG4APEX}: 
  azim[i,j]  - 1.448
  -0.266*(y1[i,j]-2) + 0.295*(y2[i,j]-2) + 0.57*(y3[i,j]-2)
  -0.745*(sqrt8-2.52)  +0.268*(y5[i,j]-2) + 0.385*(y6[i,j]-2.52) >= 0;

# permute the y coordinates so that [i,j] is the apiece dart
# y6 is opposite, y5 is other long in APIECE.
apieceazim3 'ID[1812128999]' {(i1,i,i3,j) in EDART: (i,j) in APIECE}: 
  azim[i1,j]  - 1.448
  -0.266*(y3[i,j]-2) + 0.295*(y1[i,j]-2) + 0.57*(y2[i,j]-2)
  -0.745*(y6[i,j]-2.52)  +0.268*(y4[i,j]-2) + 0.385*(y5[i,j]-2.52) >= 0;

# Three more obtained from preceding by y2<->y3, y5<->y6.
# darts with y4>= 2.52, y5 [2.52,s8], others [2,2.52]
big5azim56 'ID[1812128999]' {(i1,i2,i,j) in EDART: (i1,j) in BIG5APEX}: 
  azim[i,j]  - 1.448
  -0.266*(y1[i,j]-2) + 0.295*(y3[i,j]-2) + 0.57*(y2[i,j]-2)
  -0.745*(2.52-2.52)  +0.268*(y6[i,j]-2) + 0.385*(y5[i,j]-2.52) >= 0;

big4azim56 'ID[1812128999]' {(i1,i2,i,j) in EDART: (i1,j) in BIG4APEX}: 
  azim[i,j]  - 1.448
  -0.266*(y1[i,j]-2) + 0.295*(y3[i,j]-2) + 0.57*(y2[i,j]-2)
  -0.745*(sqrt8-2.52)  +0.268*(y6[i,j]-2) + 0.385*(y5[i,j]-2.52) >= 0;

# permute the y coordinates so that [i,j] is the apiece dart
# y5 is opposite, y6 is other long.
apieceazim2 'ID[1812128999]' {(i1,i,i3,j) in EDART: (i,j) in APIECE}: 
  azim[i3,j]  - 1.448
  -0.266*(y2[i,j]-2) + 0.295*(y1[i,j]-2) + 0.57*(y3[i,j]-2)
  -0.745*(y5[i,j]-2.52)  +0.268*(y4[i,j]-2) + 0.385*(y6[i,j]-2.52) >= 0;

#branch APIECE inequality.

#branch BIGTRI inequality
#branch SMALLTRI inequality
#branch HIGHVERTEX inequality
#branch LOWVERTEX inequality


solve;
display hypermapID;
display lnsum;
