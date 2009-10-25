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
* 5-way split on a standard quad, according to SUPERDUPERQ, SUPERFLAT one way, SUPERFLATS other way, flats one way, flats the other way.  The SUPERDUPERQ has both diags at least 3, the SUPERFLAT has both diags at least sqrt(8), and the shorter diagonal at most 3.  The SUPERFLAT always splits along the shorter diagonal.   A flat has a diagonal at most sqrt(8).
* 11-way split on std. pent, SUPER8, 5 (flat+big4face), 5 (flat+flat+Apiece).
* 6-way split on std. hex, SUPER8, 6 (flat+big5face).
Note that a big5face may have other flats within it, that are not used in branching.  This is done to keep the branching on hexagons to a minimum.

****************

Sets provided in the data file :
hypermapID: a numerical identifier of the case.
CVERTEX: the number of vertices. 
CFACE: the number of faces.  Standard regions that have been subdivided are not counted.
EDART: quadruples (i1,i2,i3,j) where (i1,j) is a dart such that f(i1,j) = (i2,j), f(i2,j)=(i3,j).
ITRIANGLE, IQUAD, IPENT, IHEX:  standard faces with 3,4,5,6 darts.  Includes special cases such as SUPERDUPERQ, SUPER8, ..
SUPERDUPERQ: quads with both diags at least 3. It is the dart opposite the long edge.
SUPERFLAT: apex of superflat triangulating a quad with shorter diagonal at least sqrt8-3.
SUPER8: pents, and hexes that are known not to have any flat quarters.  
FLAT: the apex darts of flat quarters.  It is the dart opposite the long edge.
APIECE: the apex darts of type A triangle in triangulation of pentagon
BIG5APEX: apex dart of complement of flat in hex, where the apex dart is defined as 
  in the BIG4APEX.  It is *not* the dart opposite the long edge.
BIG4APEX: apex dart in complement of flat in pent, where the apex dart is defined as
  the dart x s.t. f x and f^2 x are the two darts along the long edge.
BIGEDGE: edge ye >= 2.25;
SMALLEDGE: edge ye <= 2.25;
BIGTRI: standard triangles with y4+y5+y6>=6.25;
SMALLTRI: standard triangles with y4+y5+y6<=6.25;
HIGHVERTEX: vertex with yn >= 2.18;
EXTRAHIGHVERTEX: vertex with yn >= 2.36;
MEDIUMHIGHVERTEX: vertex with yn >= 2.18 <= 2.36;
LOWVERTEX: vertex with yn <= 2.18;

*/

param hypermapID;
param pi := 3.1415926535897932;
param delta0 := 0.5512855984325308;
param tgt := 1.54065864570856;
param sqrt8 := 2.8284271247461900;
param rho218 := 1.0607429578779386; # constant is rho(2.18).
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
set STANDARD := ITRIANGLE union IQUAD union IPENT union IHEX; # standard regions.
set IDART3:= {(i,j) in DART: j in ITRIANGLE};
set IDART4:= {(i,j) in DART: j in IQUAD};
set ALLTRI:= setof {(i1,i2,i3,j1,k1,k2,k3,j2) in EDART cross EDART: (j1 = j2) and (i2=k1) and (i3=k2) and (i1=k3)} (i1,j1);

# branch sets
set SUPER8 within  IPENT union IHEX;
set SUPERDUPERQ within (IQUAD diff SUPER8);
set SUBREGION := FACE diff STANDARD;
set FLAT within {(i,j) in DART : j in SUBREGION};
set SUPERFLAT within {(i,j) in DART : j in SUBREGION};
set APIECE within {(i,j) in DART : j in SUBREGION};

# APEX3 does not include all darts of FLAT, SUPERFLAT, and APIECE, only the distinguished one.
set APEX3 := FLAT union APIECE union SUPERFLAT union IDART3;
set BIG5APEX within {(i,j) in DART : j in SUBREGION};  
set BIG4APEX within {(i,j) in DART: j in SUBREGION};  
set BIGTRI within ITRIANGLE;
set SMALLTRI within ITRIANGLE;
set BIGEDGE within IDART3;
set SMALLEDGE within IDART3;
set HIGHVERTEX within IVERTEX;
set EXTRAHIGHVERTEX within HIGHVERTEX;
set MEDIUMHIGHVERTEX within HIGHVERTEX;
set LOWVERTEX within IVERTEX;

## SPECIAL SETS OF DARTS ##

# parts of darts of opposite vertices of SUPERFLATS:
set SUPERFLATPAIR := setof {(i1,i2,i3,j1,i4,k3,k2,j2) in EDART cross EDART: (i1,j1) in SUPERFLAT and (i4,j2) in SUPERFLAT and (i2=k2) and (i3=k3)} (i1,j1,i4,j2);

# darts with opposite at least 2.52 others in [2,2.52].
set DARTX :=  BIG5APEX union
   setof{(i1,i2,i3,j) in EDART: (i3,j) in BIG5APEX}(i1,j) union
   setof{(i1,i2,i3,j) in EDART: (i3,j) in BIG5APEX}(i2,j) union
   {(i,j) in DART: j in IQUAD union IPENT union IHEX};

# darts with opposite at least s8, others in [2,2.52].
set DARTY := SUPERFLAT union BIG4APEX union
    setof{(i1,i2,i3,j) in EDART : (i2,j) in BIG4APEX}(i1,j);

# darts with opposite at least 3, others in [2,2.52].
set DARTZ := {(i,j) in DART: j in SUPERDUPERQ};

# all LOWVERTEX darts
set LOWTRI := setof{(i1,i2,i3,j) in EDART : 
   i1 in LOWVERTEX and
   i2 in LOWVERTEX and
   i3 in LOWVERTEX and
    j in ITRIANGLE}(i2,j);

# high-low-low

set HLLTRI := setof{(i1,i2,i3,j) in EDART : 
   i1 in LOWVERTEX and
   i2 in HIGHVERTEX and
   i3 in LOWVERTEX and
   j in ITRIANGLE}(i2,j);


set LOWSMALLTRI := {(i,j) in LOWTRI :   j in SMALLTRI};

set LOWBIGTRI := {(i,j) in LOWTRI :    j in BIGTRI};

set HLLSMALLTRI := {(i,j) in HLLTRI : j in SMALLTRI};

# basic variables
var azim{DART} >= 0, <= pi;
var azim2{HLLTRI} >=0, <= pi;
var azim3{HLLTRI} >=0, <= pi;
var ln{IVERTEX} >= 0, <= 1;
var rhzim{DART} >=0, <= pi + delta0;
var yn{IVERTEX} >= 2, <= 2.52;
var ye{DEDGE} >= 2, <= 3;
var rho{IVERTEX} >= 1, <= 1 + delta0/pi;
var sol{FACE} >= 0, <= 4.0*pi;
var tau{FACE} >= 0, <= tgt;
var y1{DART} >= 2, <=2.52;
var y2{DART} >=2, <=2.52;
var y3{DART} >=2, <=2.52;
var y4{ALLTRI} >=2, <=3;
var y5{DEDGE} >=2, <=3;
var y6{DEDGE} >=2, <=3;


#report variables
var lnsum;
var ynsum;
var sqdeficit;

## objective
maximize objective:  lnsum;

## equality constraints
lnsum_def: sum{i in IVERTEX} ln[i]  = lnsum;
ynsum_def: sum{i in IVERTEX} yn[i] = ynsum;
sqdeficit_def: tgt - sum{j in FACE} tau[j] = sqdeficit;
azim_sum{i in IVERTEX}:  sum {(i,j) in DART} azim[i,j] = 2.0*pi;
rhzim_sum{i in IVERTEX}:  sum {(i,j) in DART} rhzim[i,j] = 2.0*pi*rho[i];
sol_sum{j in FACE}: sum{(i,j) in DART} (azim[i,j] - pi) = sol[j] - 2.0*pi;
tau_sum{j in FACE}: sum{(i,j) in DART} (rhzim[i,j] - pi -delta0) = tau[j] - 2.0*(pi+delta0);



ln_def{i in IVERTEX}: ln[i] = (2.52 - yn[i])/0.52;
rho_def{i in IVERTEX}: rho[i] = (1 + delta0/pi) - ln[i] * delta0/pi;
edge{(i1,j1,i2,j2) in EDGE}: ye[i1,j1] = ye[i2,j2];
y1_def{(i3,i1,i2,j) in EDART}: y1[i1,j] = yn[i1];
y2_def{(i3,i1,i2,j) in EDART}: y2[i1,j] = yn[i2];
y3_def{(i3,i1,i2,j) in EDART}: y3[i1,j] = yn[i3];
y4_def{(i3,i1,i2,j) in EDART :  (i1,j) in ALLTRI}: y4[i1,j] = ye[i2,j];
y5_def{(i3,i1,i2,j) in EDART}: y5[i1,j] = ye[i3,j];
y6_def{(i3,i1,i2,j) in EDART}: y6[i1,j] = ye[i1,j];
azim2c{(i1,i2,i3,j) in EDART : (i2,j) in HLLTRI}: azim2[i2,j] = azim[i3,j];
azim3c{(i1,i2,i3,j) in EDART : (i2,j) in HLLTRI}: azim3[i2,j] = azim[i1,j];

## inequality constraints
main: sum{i in IVERTEX} ln[i] >= 12;
RHA{(i,j) in DART}: rhzim[i,j] >= azim[i,j]*1.0;
RHB{(i,j) in DART}: rhzim[i,j] <= azim[i,j]*(1+delta0/pi);
RHBLO{(i,j) in DART: i in LOWVERTEX}: rhzim[i,j] <= azim[i,j]*rho218;
RHBHI{(i,j) in DART: i in HIGHVERTEX}: rhzim[i,j] >= azim[i,j]*rho218;

## branch definitional inequalities
ybig{(i,j) in IDART3 : j in BIGTRI}: 
  y4[i,j]+y5[i,j]+y6[i,j] >= 6.25;
ysmall{(i,j) in IDART3 : j in SMALLTRI}: 
  y4[i,j]+y5[i,j]+y6[i,j] <= 6.25;
yhigh{i in HIGHVERTEX}: yn[i] >= 2.18;
ylow{i in LOWVERTEX}: yn[i] <= 2.18;
yextrahigh{i in EXTRAHIGHVERTEX}: yn[i] >= 2.36;
ymediumhigh{i in MEDIUMHIGHVERTEX}: yn[i] <= 2.36;
yebig{(i,j) in BIGEDGE}: ye[i,j] >= 2.25;
yesmall{(i,j) in SMALLEDGE}: ye[i,j] <= 2.25;

# y bounds.
ye3_bound{(i,j) in DART : j in STANDARD}: ye[i,j] <= 2.52;
y4_boundF{(i,j) in FLAT}: y4[i,j] >= 2.52;
y4_boundL{(i,j) in SUPERFLAT}: y4[i,j] >= sqrt8;
y5_boundF{(i,j) in FLAT union SUPERFLAT}: y5[i,j] <= 2.52;
y6_boundF{(i,j) in FLAT union SUPERFLAT}: y6[i,j] <= 2.52;
y4_boundA{(i,j) in ALLTRI diff SUPERFLAT}: y4[i,j] <= sqrt8;
y4_boundAp{(i,j) in APIECE}: y4[i,j] <= 2.52; # others redun. via FLAT
# y4_boundS{(i,j) in SUPERFLAT}: y4[i,j] <= 3; # redundant via ye.
# BIGAPEX4 BIGAPEX5: covered by neighbors unless there are 2.


# tau inequality (Main Estimate)

tau3{j in ITRIANGLE}: tau[j] >= 0;
tau4{j in IQUAD}: tau[j] >= 0.206;
tau5{j in IPENT}: tau[j] >= 0.4819;
tau6{j in IHEX}: tau[j] >= 0.7578;

## interval arithmetic bounds IDART3 ##

azmin 'ID[5735387903]' {(i,j) in IDART3} : azim[i,j] >= 0.852;

azmax 'ID[5490182221]' {(i,j) in IDART3}: azim[i,j] <= 1.893;

tau_azim3A 'ID[3296257235]' {(i,j) in IDART3}: 
  tau[j]+0.626*azim[i,j] - 0.77 >= 0;

tau_azim3B 'ID[8519146937]' {(i,j) in IDART3}: 
  tau[j]-0.259*azim[i,j] + 0.32 >= 0;

tau_azim3C 'ID[4667071578]' {(i,j) in IDART3}: 
  tau[j]-0.507*azim[i,j] + 0.724 >= 0;

tau_azim3D 'ID[1395142356]' {(i,j) in IDART3}: 
  tau[j] + 0.001 -0.18*(y1[i,j]+y2[i,j]+y3[i,j]-6) - 0.125*(y4[i,j]+y5[i,j]+y6[i,j]-6) >= 0;

solyA 'ID[7394240696]' {(i,j) in IDART3}: 
  sol[j] - 0.55125 - 0.196*(y4[i,j]+y5[i,j]+y6[i,j]-6) + 0.38*(y1[i,j]+y2[i,j]+y3[i,j]-6) >= 0;

solyB 'ID[7726998381]' {(i,j) in IDART3}: 
  -sol[j] + 0.5513 + 0.3232*(y4[i,j]+y5[i,j]+y6[i,j]-6) - 0.151*(y1[i,j]+y2[i,j]+y3[i,j]-6) >= 0;

azminA 'ID[4047599236]'  {(i,j) in IDART3}: azim[i,j] - 1.2308 
  + 0.3639*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.235*(y1[i,j]-2) - 0.685*(y4[i,j]-2) >= 0;

azmaxA 'ID[3526497018]' {(i,j) in IDART3}: -azim[i,j] + 1.231 
  - 0.152*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) + 0.5*(y1[i,j]-2) + 0.773*(y4[i,j]-2) >= 0;


rhazminA 'ID[5957966880]' {(i,j) in IDART3}: rhzim[i,j] - 1.2308 
  + 0.3639*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.6*(y1[i,j]-2) - 0.685*(y4[i,j]-2) >= 0;



## interval arithmetic bounds IDART4 ##

tau_azim4A 'ID[7043724150]' {(i,j) in IDART4}:
  tau[j] + 4.72*azim[i,j] - 6.248 >= 0;

tau_azim4B 'ID[6944699408]' {(i,j) in IDART4}:
  tau[j] + 0.972*azim[i,j] - 1.707 >= 0;

tau_azim4C 'ID[4240815464]' {(i,j) in IDART4}:
  tau[j] + 0.7573*azim[i,j] - 1.4333 >= 0;

tau_azim4D 'ID[3862621143]' {(i,j) in IDART4}:
  tau[j] - 0.453*azim[i,j] + 0.777 >= 0;  # typo corrected Sep 8 2009 (Thanks to Erin Susick!)

## MAIN ESTIMATE SUPER8 BIG4 BIG5 ##

tau3h {(i,j) in FLAT}: tau[j] >= 0.103;
tauAh {(i,j) in APIECE}: tau[j] >= 0.2759;
tauB4h {(i,j) in BIG4APEX}: tau[j] >= 0.492;
tauB5h {(i,j) in BIG5APEX}: tau[j] >= 0.657;
tau4s 'ID[9563139965]' {j in SUPERDUPERQ}: tau[j] >= 0.496;
tau5h{j in IPENT inter SUPER8}: tau[j] >= 0.751;
tau6h{j in IHEX inter SUPER8}: tau[j] >= 0.91;

perimZ 'ID[]' {(i1,i2,i3,j) in EDART : j in SUPERDUPERQ}:
  y5[i1,j] + y6[i1,j] + y5[i3,j] + y6[i3,j] >= 8.472;

#this kills all superduperq
tauZ 'ID[] 49c' {(i1,i2,i3,j) in EDART : j in SUPERDUPERQ}:
#  tau[j] - 0.45 *(y5[i1,j] + y6[i1,j] + y5[i3,j] + y6[i3,j]-8.472) >= 0.49;
tau[j] - 0.45 *(y5[i1,j] + y6[i1,j] + y5[i3,j] + y6[i3,j]-8.472) >= 0.46;



## more interval arithmetic on nonstandard triangles  ##

azminX 'ID[3020140039]' {(i,j) in DARTX}: 
  azim[i,j] - 1.629  + 0.402*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.315*(y1[i,j]-2)  >= 0;

azminY 'ID[9414951439]' {(i,j) in DARTY}:
  azim[i,j] - 1.91 + 0.458 * (y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.342*(y1[i,j]-2) >= 0;

azminZ 'ID[9995621667]' {(i,j) in DARTZ}:
  azim[i,j] - 2.09 + 0.578 * (y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.54*(y1[i,j]-2) >= 0;





#branch FLAT inequality

flattau 'ID[8248508703]' {(i,j) in FLAT}:
  tau[j] - 0.1 - 0.265*(y5[i,j]+y6[i,j]-4) - 0.06*(y4[i,j]-2.52) 
   - 0.16*(y1[i,j]-2) -  0.115*(y2[i,j]+y3[i,j]-4) >=0;

flatazim 'ID[3318775219]' {(i,j) in FLAT}:
  azim[i,j] - 1.629 + 0.414*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8)
-0.763*(y4[i,j]-2.52) - 0.315*(y1[i,j]-2) >= 0;

flatazimmax 'ID[9922699028]' {(i,j) in FLAT}:
  -azim[i,j] + 1.6294 - 0.2213*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8)
  +0.913*(y4[i,j]-2.52) + 0.728*(y1[i,j]-2) >= 0;

flatazim2 'ID[5000076558]' {(i1,i,i3,j) in EDART : (i,j) in FLAT}:
  azim[i3,j] - 1.083 + 0.6365*(y1[i,j]-2) - 0.198*(y2[i,j]-2)
  +0.352*(y3[i,j]-2) + 0.416*(y4[i,j]-2.52)
  -0.66*(y5[i,j]-2) + 0.071*(y6[i,j]-2) >= 0;

flatazim3 'ID[5000076558]' {(i1,i,i3,j) in EDART : (i,j) in FLAT}:
  azim[i1,j] - 1.083 + 0.6365*(y1[i,j]-2) - 0.198*(y3[i,j]-2)
  +0.352*(y2[i,j]-2) + 0.416*(y4[i,j]-2.52)
  -0.66*(y6[i,j]-2) + 0.071*(y5[i,j]-2) >= 0;

flatrhzim 'ID[9251360200]' {(i,j) in FLAT}:
  rhzim[i,j]
  -1.629 - 0.866*(y1[i,j]-2) + 0.3805*(y2[i,j]+y3[i,j]-4)
  -0.841*(y4[i,j]-2.52) + 0.501*(y5[i,j]+y6[i,j]-4) >= 0;

flatrhzim2 'ID[9756015945]' {(i1,i,i3,j) in EDART: (i,j) in FLAT}:
  rhzim[i3,j] -1.08
  +0.6362*(y1[i,j]-2) -0.565*(y2[i,j]-2)+0.359*(y3[i,j]-2)
  +0.416*(y4[i,j]-2.52) -0.666*(y5[i,j]-2) +0.061*(y6[i,j]-2) >=0;

flatrhzim3 'ID[9756015945]' {(i1,i,i3,j) in EDART: (i,j) in FLAT}:
  rhzim[i3,j] -1.08
  +0.6362*(y1[i,j]-2) -0.565*(y3[i,j]-2)+0.359*(y2[i,j]-2)
  +0.416*(y4[i,j]-2.52) -0.666*(y6[i,j]-2) +0.061*(y5[i,j]-2) >=0;

#branch azim APIECE-BIGPIECE inequality
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

#branch SUPERFLAT inequality


tausf2 'ID[4840774900]'  {(i,j) in SUPERFLAT}:
 tau[j]     -0.1054 
    -0.14132*(y1[i,j]+ y2[i,j]/2 + y3[i,j]/2 - 4)
    -0.36499*(y5[i,j]+y6[i,j]-4) >= 0;

tausf3 'ID[5451229371]'  {(i1,j1,i2,j2) in SUPERFLATPAIR}:
 tau[j1]+tau[j2]  - 0.24
    -0.14132*(y1[i1,j1]+ y2[i1,j1] + y3[i1,j1] + y1[i2,j2] - 8)
    -0.38*(y5[i1,j1]+y6[i1,j1]+y5[i2,j2]+y6[i2,j2] -8) >= 0;

tausf4 'ID[1642527039]'  {(i,j) in SUPERFLAT}:
 tau[j]     -0.128 
- 0.053*((y5[i,j]+y6[i,j]-4) - (2.75/2)*(y4[i,j]- sqrt8)) >= 0;

tausf5 'ID[7863247282]' {(i,j) in SUPERFLAT}:
 tau[j] - 0.053*((y5[i,j]+y6[i,j]-4) - (2.75/2)*(y4[i,j]- sqrt8))
    -0.12 
    -0.14132*(y1[i,j]+ y2[i,j]/2 + y3[i,j]/2 - 4)
    -0.328*(y4[i,j]+y5[i,j]-4) >= 0;

ysuperflat 'ID[8673686234]' {(i1,j1,i2,j2) in SUPERFLATPAIR}:
   (y5[i1,j1]+y6[i1,j1]+y5[i2,j2]+y6[i2,j2]-8) >= 2.75*(y4[i1,j1]-sqrt8);

azimf3 'ID[7718591733]' {(i,j) in SUPERFLAT}:
  azim[i,j] - 0.955 
   - 0.2356*(y1[i,j]-2)
       +0.32*(y2[i,j]-2) + 0.792*(y3[i,j]-2)
   -0.707*(y4[i,j]-2) 
        + 0.0844*(y5[i,j]-2) + 0.821*(y6[i,j]-sqrt8) >=0;


azimsf2 'ID[3566713650]' {(i,j) in SUPERFLAT}:
  -azim[i,j] + 1.911 +1.01 *(y1[i,j] - 2)
  -0.284*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8)
   +1.07*(y4[i,j]-sqrt8) >= 0;


azimsf1 'ID[1085358243]' {(i,j) in SUPERFLAT}:
  azim[i,j] - 1.903 - 0.4*(y1[i,j] - 2)
  +0.49688*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8)
   -(y4[i,j]-sqrt8) >= 0;

# this one based on fact that crossdiag of superflat is longer than diag.
# y4[i1,j1] is the diag, which is shorter than the cross diag. 
# By monotonicity of dih in opposite edge length, this may be substituted in.
crossdiag 'ID[1085358243]+' 
   {(i1,i,i3,j1,k1,k2,k3,j2) in EDART cross EDART :
     i = k3 and i3 = k2 and (i1,j1,k1,j2) in SUPERFLATPAIR}:
  (azim[i,j1]+azim[i,j2]) - 1.903 - 0.4*(y1[i,j1] - 2)
  +0.49688*(y2[i,j2]+y3[i,j1]+y5[i,j1]+y6[i,j2]-8)
   -(y4[i1,j1]-sqrt8) >= 0;




#branch APIECE inequality.

apieceazim 'ID[5760733457]' {(i,j) in APIECE}:
  azim[i,j] - 1.0705 
  -0.1*(y1[i,j]-2) + 0.424*(y2[i,j]-2) + 0.424*(y3[i,j]-2) 
  -0.594*(y4[i,j]-2) + 0.124*(y5[i,j]-2.52) + 0.124*(y6[i,j]-2.52) >= 0;

apiecerhzim 'ID[2563100177]' {(i,j) in APIECE}:
  rhzim[i,j] - 1.0685 
  -0.4635*(y1[i,j]-2) + 0.424*(y2[i,j]-2) + 0.424*(y3[i,j]-2) 
  -0.594*(y4[i,j]-2) + 0.124*(y5[i,j]-2.52) + 0.124*(y6[i,j]-2.52) >= 0;

apiecetau 'ID[7931207804]' {(i,j) in APIECE}:
  tau[j] - 0.27
  +0.0295*(y1[i,j]-2) - 0.0778*(y2[i,j]-2) - 0.0778*(y3[i,j]-2) 
  -0.37*(y4[i,j]-2) - 0.27*(y5[i,j]-2.52) - 0.27*(y6[i,j]-2.52) >= 0;





#branch SMALLTRI inequality

smalltritau 'ID[9225295803]' {(i,j) in DART: j in SMALLTRI}:
  tau[j] +0.0034
  -0.166*(y1[i,j]+y2[i,j]+y3[i,j]-6) -0.22*(y4[i,j]+y5[i,j]+y6[i,j]-6) >=0;

smalltridih 'ID[9291937879]' {(i,j) in DART: j in SMALLTRI}:
  azim[i,j] - 1.23
  -0.235*(y1[i,j]-2) + 0.362*(y2[i,j]+y3[i,j]-4)
  -0.694*(y4[i,j]-2) + 0.26*(y5[i,j]+y6[i,j]-4) >=0;

#branch BIGTRI inequality

bigtritau 'ID[7761782916]' {(i,j) in DART: j in BIGTRI}:
  tau[j] - 0.05 -0.137*(y1[i,j]+y2[i,j]+y3[i,j]-6)
  -0.17*(y4[i,j]+y5[i,j]+y6[i,j]-6.25) >= 0;

bigtrisol 'ID[6224332984]'  {(i,j) in DART: j in BIGTRI}:
  sol[j] - 0.589 +0.39*(y1[i,j]+y2[i,j]+y3[i,j]-6)
  -0.235*(y4[i,j]+y5[i,j]+y6[i,j]-6.25) >= 0;



#branch LOWSMALLVERTEX inequality

azimlowsmall 'ID[9229542852]' {(i,j) in LOWSMALLTRI}:
  azim[i,j] - 1.230
  -0.2357*(y1[i,j]-2)
  +0.2493*(y2[i,j]+y3[i,j]-4)
  -0.682*(y4[i,j]-2)
  +0.3035*(y5[i,j]+y6[i,j]-4) >= 0;

azimlowsmallmax 'ID[1550635295]' {(i,j) in LOWSMALLTRI}:
  -azim[i,j] + 1.232
  +0.261*(y1[i,j]-2)
  -0.203*(y2[i,j]+y3[i,j]-4)
  +0.772*(y4[i,j]-2)
  -0.191*(y5[i,j]+y6[i,j]-4) >= 0;

taulowsmall 'ID[4491491732]' {(i,j) in LOWSMALLTRI}:
  tau[j]  + 0.0008
  -0.1631*(y1[i,j]+y2[i,j]+y3[i,j]-6)
  -0.2127*(y4[i,j]+y5[i,j]+y6[i,j]-6) >= 0;

taulowbig 'ID[8611785756]'  {(i,j) in LOWBIGTRI}:
  sol[j] - 0.589 +0.24*(y1[i,j]+y2[i,j]+y3[i,j]-6)
  -0.16*(y4[i,j]+y5[i,j]+y6[i,j]-6.25) >= 0;

#branch HIGH VERTEX inequality

hiazimA 'ID[2151506422]' {(i,j) in HLLTRI} :
   azim[i,j] >= 1.2777 
     + 0.281*(y1[i,j]-2.18)
     - 0.278364*(y2[i,j]-2)
     -0.278364*(y3[i,j]-2)
     + 0.7117*(y4[i,j]-2)
      -0.34336*(y5[i,j]-2) 
      -0.34336*(y6[i,j]-2);

hiazimB 'ID[6836427086]' {(i,j) in HLLTRI} :
   -azim[i,j] >= -1.27799
     -0.356217*(y1[i,j]-2.18)
     +0.229466*(y2[i,j]-2)
     +0.229466*(y3[i,j]-2)
     -0.949067*(y4[i,j]-2)
     +0.172726*(y5[i,j]-2) 
     +0.172726*(y6[i,j]-2);
     #{-0.356217, 0.229466, 0.229466, -0.949067, 0.172726, 0.172726}

hiazimC 'ID[3636849632]' {(i,j) in HLLTRI} :
   tau[j] >=  0.0345
     +0.185545*(y1[i,j]-2.18)
     +0.193139*(y2[i,j]-2)
     +0.193139*(y3[i,j]-2)
     +0.170148*(y4[i,j]-2)
     +0.13195*(y5[i,j]-2) 
     +0.13195*(y6[i,j]-2);
     #{0.185545, 0.193139, 0.193139, 0.170148, 0.13195, 0.13195}

hiazimD 'ID[5298513205]' {(i,j) in HLLTRI} :
   azim2[i,j] >= 1.185
     -0.302913*(y1[i,j]-2.18)
     +0.214849*(y2[i,j]-2)
     -0.163775*(y3[i,j]-2)
     -0.443449*(y4[i,j]-2)
     +0.67364*(y5[i,j]-2) 
     -0.314532*(y6[i,j]-2);
     # {-0.302913, 0.214849, -0.163775, -0.443449, 0.67364, -0.314532}

hiazimE 'ID[5298513205]' {(i,j) in HLLTRI} : # 2<->3, 5<->6 sym.
   azim3[i,j] >= 1.185
     -0.302913*(y1[i,j]-2.18)
     +0.214849*(y3[i,j]-2)
     -0.163775*(y2[i,j]-2)
     -0.443449*(y4[i,j]-2)
     +0.67364*(y6[i,j]-2) 
     -0.314532*(y5[i,j]-2);
     # {-0.302913, 0.214849, -0.163775, -0.443449, 0.67364, -0.314532}

hiazimF 'ID[7743522046]' {(i,j) in HLLTRI} :
   -azim2[i,j] >= -1.1865
     +0.20758*(y1[i,j]-2.18)
     -0.236153*(y2[i,j]-2)
     +0.14172*(y3[i,j]-2)
     +0.263834*(y4[i,j]-2)
     -0.771203*(y5[i,j]-2) 
     +0.0457292*(y6[i,j]-2);
     #{0.20758, -0.236153, 0.14172, 0.263834, -0.771203, 0.0457292};

hiazimG 'ID[7743522046]' {(i,j) in HLLTRI} : # 2<->3, 5<->6 sym.
   -azim3[i,j] >= -1.1865
     +0.20758*(y1[i,j]-2.18)
     -0.236153*(y3[i,j]-2)
     +0.14172*(y2[i,j]-2)
     +0.263834*(y4[i,j]-2)
     -0.771203*(y6[i,j]-2) 
     +0.0457292*(y5[i,j]-2);
     #{0.20758, -0.236153, 0.14172, 0.263834, -0.771203, 0.0457292};

# branch HLL SMALL 

hllsmallazimA 'ID[8657368829]' {(i,j) in HLLTRI : j in SMALLTRI} :
   azim[i,j] >= 1.277
     +0.273298*(y1[i,j]-2.18)
     -0.273853*(y2[i,j]-2)
     -0.273853*(y3[i,j]-2)
     +0.708818*(y4[i,j]-2)
     -0.313988*(y5[i,j]-2) 
     -0.313988*(y6[i,j]-2);
     #{0.273298, -0.273853, -0.273853, 0.708818, -0.313988, -0.313988}


hllsmallazimB 'ID[6619134733]' {(i,j) in HLLTRI : j in SMALLTRI} :
   -azim[i,j] >= -1.27799
     -0.439002*(y1[i,j]-2.18)
     +0.229466*(y2[i,j]-2)
     +0.229466*(y3[i,j]-2)
     -0.771733*(y4[i,j]-2)
      +0.208429*(y5[i,j]-2) 
     +0.208429*(y6[i,j]-2);
     # {-0.439002, 0.229466, 0.229466, -0.771733, 0.208429, 0.208429}

hllsmallazimC 'ID[1284543870]' {(i,j) in HLLTRI : j in SMALLTRI} :
   azim2[i,j] >= 1.185
     -0.372262*(y1[i,j]-2.18)
     +0.214849*(y2[i,j]-2)
     -0.163775*(y3[i,j]-2)
     -0.293508*(y4[i,j]-2)
     +0.656172*(y5[i,j]-2) 
     -0.267157*(y6[i,j]-2);
   # {-0.372262, 0.214849, -0.163775, -0.293508, 0.656172, -0.267157};

hllsmallazimD 'ID[1284543870]' {(i,j) in HLLTRI : j in SMALLTRI} :
   azim3[i,j] >= 1.185  
     -0.372262*(y1[i,j]-2.18)
     +0.214849*(y3[i,j]-2)
     -0.163775*(y2[i,j]-2)
     -0.293508*(y4[i,j]-2)
     +0.656172*(y6[i,j]-2) 
     -0.267157*(y5[i,j]-2);
   # {-0.372262, 0.214849, -0.163775, -0.293508, 0.656172, -0.267157};

hllsmallazimE 'ID[4041673283]' {(i,j) in HLLTRI : j in SMALLTRI} :
   -azim2[i,j] >= -1.1864
     +0.20758*(y1[i,j]-2.18)
     -0.236153*(y2[i,j]-2)
     +0.14172*(y3[i,j]-2)
     +0.263109*(y4[i,j]-2)
     -0.737003*(y5[i,j]-2) 
     +0.12047*(y6[i,j]-2);
  #{0.20758, -0.236153, 0.14172, 0.263109, -0.737003, 0.12047};

hllsmallazimF 'ID[4041673283]' {(i,j) in HLLTRI : j in SMALLTRI} :
   -azim3[i,j] >= -1.1864  # symmetry 2<->3, 5<->6.
     +0.20758*(y1[i,j]-2.18)
     -0.236153*(y3[i,j]-2)
     +0.14172*(y2[i,j]-2)
     +0.263109*(y4[i,j]-2)
     -0.737003*(y6[i,j]-2) 
     +0.12047*(y5[i,j]-2);
  #{0.20758, -0.236153, 0.14172, 0.263109, -0.737003, 0.12047};


# branch FLAT:

tauhighlow 'ID[8282573160]'  
  {(i1,i,i3,j) in EDART : i1 in LOWVERTEX and i in HIGHVERTEX and 
               i3 in LOWVERTEX and (i,j) in FLAT}:
  tau[j] - 0.1413
  -0.214*(y1[i,j]-2.18)
  -0.1259*(y2[i,j]+y3[i,j]-4)
  -0.067*(y4[i,j]-2.52)
  -0.241*(y5[i,j]+y6[i,j]-4) >=0;


# branch BIG/SMALL/EDGE EXTRAHIGH/MEDIUMHIGH

#a
azim_med_big 'ID[3872614111]' {(i,i2,i3,j) in EDART : (i2,j) in BIGEDGE and (i,j) in HLLTRI and i in MEDIUMHIGHVERTEX}:
  -azim[i,j] >= -1.542
     -0.362519*(y1[i,j]-2.36)
      +0.298691*(y2[i,j]-2)
      +0.287065*(y3[i,j]-2)
      -0.920785*(y4[i,j]-2.25)
      +0.190917*(y5[i,j]-2)
      +0.219132*(y6[i,j]-2) ;
   #  {-0.362519, 0.298691, 0.287065, -0.920785, 0.190917, 0.219132};

#b
azim_med_small 'ID[3139693500]' {(i,i2,i3,j) in EDART : (i2,j) in SMALLEDGE and (i,j) in HLLTRI and i in MEDIUMHIGHVERTEX}:
  -azim[i,j] >= -1.542
     -0.346773*(y1[i,j]-2.36)
      +0.300751*(y2[i,j]-2)
      +0.300751*(y3[i,j]-2)
      -0.702567*(y4[i,j]-2.25)
      +0.172726*(y5[i,j]-2)
      +0.172727*(y6[i,j]-2) ;
   # {-0.346773, 0.300751, 0.300751, -0.702567, 0.172726, 0.172727};


#c
azim2_extra_small 'ID[4841020453]' {(i,i2,i3,j) in EDART : (i2,j) in SMALLEDGE and (i,j) in HLLTRI and i in EXTRAHIGHVERTEX}:
  -azim[i,j] >= -1.542
     -0.490439*(y1[i,j]-2.36)
      +0.318125*(y2[i,j]-2)
      +0.32468*(y3[i,j]-2)
      -0.740079*(y4[i,j]-2.25)
      +0.178868*(y5[i,j]-2)
      +0.205819*(y6[i,j]-2) ;
   #  {-0.490439, 0.318125, 0.32468, -0.740079, 0.178868, 0.205819};


#d
azim_extra_big 'ID[9925287433]' {(i,i2,i3,j) in EDART : (i2,j) in BIGEDGE and (i,j) in HLLTRI and i in EXTRAHIGHVERTEX}:
   -azim[i,j] >= -1.542
     -0.490439*(y1[i,j]-2.36)
      +0.321849*(y2[i,j]-2)
      +0.320956*(y3[i,j]-2)
      -1.00902*(y4[i,j]-2.25)
      +0.240709*(y5[i,j]-2)
      +0.218081*(y6[i,j]-2) ;
   # {-0.490439, 0.321849, 0.320956, -1.00902, 0.240709, 0.218081};


#e
azim2_med_big 'ID[7409690040]' {(i,i2,i3,j) in EDART : (i2,j) in BIGEDGE and (i,j) in HLLTRI and i in MEDIUMHIGHVERTEX}:
  azim2[i,j] >= 1.0494
     -0.297823*(y1[i,j]-2.36)
      +0.215328*(y2[i,j]-2)
      -0.0792439*(y3[i,j]-2)
      -0.422674*(y4[i,j]-2.25)
      +0.647416*(y5[i,j]-2)
      -0.207561*(y6[i,j]-2) ;
   #  {-0.297823, 0.215328, -0.0792439, -0.422674, 0.647416, -0.207561};

#e sym
azim3_med_big 'ID[7409690040]' {(i,i2,i3,j) in EDART : (i2,j) in BIGEDGE and (i,j) in HLLTRI and i in MEDIUMHIGHVERTEX}:
  azim3[i,j] >= 1.0494
     -0.297823*(y1[i,j]-2.36)
      +0.215328*(y3[i,j]-2)
      -0.0792439*(y2[i,j]-2)
      -0.422674*(y4[i,j]-2.25)
      +0.647416*(y6[i,j]-2)
      -0.207561*(y5[i,j]-2) ;
   #  {-0.297823, 0.215328, -0.0792439, -0.422674, 0.647416, -0.207561};


#f
azim2_med_small 'ID[4002562507]' {(i,i2,i3,j) in EDART : (i2,j) in SMALLEDGE and (i,j) in HLLTRI and i in MEDIUMHIGHVERTEX}:
  azim2[i,j] >= 1.0494
     -0.29013*(y1[i,j]-2.36)
      +0.215328*(y2[i,j]-2)
      -0.0715511*(y3[i,j]-2)
      -0.267157*(y4[i,j]-2.25)
      +0.650269*(y5[i,j]-2)
      -0.295198*(y6[i,j]-2) ;
   #  {-0.29013, 0.215328, -0.0715511, -0.267157, 0.650269, -0.295198};

#f sym
azim3_med_small 'ID[4002562507]' {(i,i2,i3,j) in EDART : (i2,j) in SMALLEDGE and (i,j) in HLLTRI and i in MEDIUMHIGHVERTEX}:
  azim3[i,j] >= 1.0494
     -0.29013*(y1[i,j]-2.36)
      +0.215328*(y3[i,j]-2)
      -0.0715511*(y2[i,j]-2)
      -0.267157*(y4[i,j]-2.25)
      +0.650269*(y6[i,j]-2)
      -0.295198*(y5[i,j]-2) ;
   #  {-0.29013, 0.215328, -0.0715511, -0.267157, 0.650269, -0.295198};


#g
azim_extra_small 'ID[5835568093]' {(i,i2,i3,j) in EDART : (i2,j) in SMALLEDGE and (i,j) in HLLTRI and i in EXTRAHIGHVERTEX}:
  azim2[i,j] >= 1.0494
     -0.404131*(y1[i,j]-2.36)
      +0.212119*(y2[i,j]-2)
      -0.0402827*(y3[i,j]-2)
      -0.299046*(y4[i,j]-2.25)
      +0.643273*(y5[i,j]-2)
      -0.266118*(y6[i,j]-2) ;
   # {-0.404131, 0.212119, -0.0402827, -0.299046, 0.643273, -0.266118};

#g sym
azim3_extra_small 'ID[5835568093]' {(i,i2,i3,j) in EDART : (i2,j) in SMALLEDGE and (i,j) in HLLTRI and i in EXTRAHIGHVERTEX}:
  azim3[i,j] >= 1.0494
     -0.404131*(y1[i,j]-2.36)
      +0.212119*(y3[i,j]-2)
      -0.0402827*(y2[i,j]-2)
      -0.299046*(y4[i,j]-2.25)
      +0.643273*(y6[i,j]-2)
      -0.266118*(y5[i,j]-2) ;
   # {-0.404131, 0.212119, -0.0402827, -0.299046, 0.643273, -0.266118};


#h
azim2_extra_big 'ID[1894886027]' {(i,i2,i3,j) in EDART : (i2,j) in BIGEDGE and (i,j) in HLLTRI and i in EXTRAHIGHVERTEX}:
  azim2[i,j] >= 1.0494
     -0.401543*(y1[i,j]-2.36)
      +0.207551*(y2[i,j]-2)
      -0.0294227*(y3[i,j]-2)
      -0.494954*(y4[i,j]-2.25)
      +0.605453*(y5[i,j]-2)
      -0.156385*(y6[i,j]-2) ;
   # {-0.401543, 0.207551, -0.0294227, -0.494954, 0.605453, -0.156385};

#h sym
azim3_extra_big 'ID[1894886027]' {(i,i2,i3,j) in EDART : (i2,j) in BIGEDGE and (i,j) in HLLTRI and i in EXTRAHIGHVERTEX}:
  azim3[i,j] >= 1.0494
     -0.401543*(y1[i,j]-2.36)
      +0.207551*(y3[i,j]-2)
      -0.0294227*(y2[i,j]-2)
      -0.494954*(y4[i,j]-2.25)
      +0.605453*(y6[i,j]-2)
      -0.156385*(y5[i,j]-2) ;
   # {-0.401543, 0.207551, -0.0294227, -0.494954, 0.605453, -0.156385};

 

solve;
display hypermapID;
display lnsum;
display yn;
display ye;
display azim;
display rhzim;
display tau;
display sol;
display sqdeficit;
