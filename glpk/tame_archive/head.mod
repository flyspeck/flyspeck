/* ========================================================================== */
/* FLYSPECK - Computer Code                                           */
/*                                                                            */
/* Lemma: None                                                               */
/* Chapter: Tame Hypermap                     */
/* Author: Thomas C. Hales                                                    */
/* Date: created May 8, 2009, revised June 10, 2009        */
/* ========================================================================== */

/* MathProg model for the Kepler conjecture

Revised June 15, 2010. Many sets and parameters renamed for consistency.
Many of the inequalities are automatically generated from the formal specification.

The model starts with a tame hypermap, then breaks certain
quadrilaterals into two flats, certain pentagons into a flat+big4face
or into 2 flats+apiece, certain hexagons into flat+big5face.  The new
internal edges of pentagons and hexagons have length 2.52--sqrt8.


  The sets std3, std4, std5, std6 index the
standard regions.  The other faces are faces of (V,E) obtained by
adding diagonals to E_std.  If a standard region with 5 or 6 darts is
has no flat quarters, then it belongs to std56_flat_free.

The term apex refers to a distinguished dart on a face.

****************

The branching has the following types.

std3: 2-way split on a triangular standard region according to
  y4+y5+y6 <= 6.25.  node: 2-way split on a node according to yn <=
  2.18

std4: 5-way split on a standard quad, according to std4_diag3,
   apex_sup_flat one way, apex_sup_flat other way, flats one
   way, flats the other way.  In these first 4 cases, a new edge (the
   diagonal) is added to (V,E).  In std4_diag3, both diags are at
   least 3, but no new edge is added to (V,E).  the apex_sup_flat
   has both diags at least sqrt(8), and the shorter diagonal at most
   3.  The apex_sup_flat always splits along the shorter
   diagonal.  A flat has a diagonal at most sqrt(8).

std5: * 11-way split on std. pent, std56_flat_free, 5
(flat+big4face), 5 (flat+flat+Apiece).  In each case except the first,
one or two new diagonals are added to (V,E).

std6: * 6-way split on std. hex, std56_flat_free, 6
(flat+big5face).  Note that a big5face may have other flats within it,
that are not used in branching.  This is done to keep the branching on
hexagons to a minimum.

****************

Sets provided in the data file :
hypermap_id: a numerical identifier of the case.
card_node: the number of nodes. 
card_face: the number of faces in the hypermap (V,E). 
e_dart: quadruples (i1,i2,i3,j) where (i1,j) is a dart such that f(i1,j) = (i2,j), f(i2,j)=(i3,j).

std3, std4, std5, std6:  standard faces with 3,4,5,6 darts.  Includes special cases such as std4_diag3, std56_flat_free, 

std4_diag3: quads with both diags at least 3. It is the dart opposite the long edge.
std56_flat_free: pents, and hexes with no flat quarters.  

std3_big: standard triangles with y4+y5+y6>=6.25;
std3_small: standard triangles with y4+y5+y6<=6.25;

apex_sup_flat: apex of super flat triangulating a quad 
   with shorter diagonal at least sqrt8-3.
apex_flat: the apex darts of flat quarters.  It is the dart opposite the long edge.
apex_A: the apex darts of type A triangle in triangulation of pentagon
apex4: apex dart in complement of flat in pent, where the apex dart is defined as
  the dart x s.t. f x and f^2 x are the two darts along the long edge.
apex5: apex dart of complement of flat in hex, where the apex dart is defined as 
  in the apex4.  It is *not* the dart opposite the long edge.

d_edge_225_252: edge ye >= 2.25;
d_edge_200_225: edge ye <= 2.25;


node_218_252: node with yn >= 2.18;
node_236_252: node with yn >= 2.36;
node_218_236: node with yn >= 2.18 <= 2.36;
node_200_218: node with yn <= 2.18;

*/

param hypermap_id;
param pi := 3.1415926535897932;
param sol0 := 0.5512855984325308;
param tgt := 1.541;  # 1.54065864570856;
param sqrt8 := 2.8284271247461900;
param rho218 := 1.0607429578779386; # constant is rho(2.18).
param card_node 'number of nodes' >= 13, <= 15; 
param card_face 'number of faces' >= 0; 


# directed edge (i,j) identified with tail of arrow.
set node := 0..(card_node-1);
set face := 0..(card_face-1);
set e_dart 'extended dart' within node cross node cross node cross face;
set dart := setof {(i1,i2,i3,j) in e_dart} (i1,j);
set d_edge := dart;
set edge within dart cross dart := 
  setof{(i1,i2,i3,j1) in e_dart,(i0,i3,i2,j2) in e_dart}(i2,j1,i3,j2);

# face sets
set std3 within face; 
set std4 within face diff std3;  
set std5 within face diff (std3 union std4); 
set std6 within face diff (std3 union std4 union std5); 
set std56_flat_free within  std5 union std6;
set std4_diag3 within std4;
set std := std3 union std4 union std5 union std6; # all standard regions.
set non_std := face diff std;
set std3_big within std3;
set std3_small within std3;

# dart sets

set dart_std3:= {(i,j) in dart: j in std3};
set dart_std3_big := {(i,j) in dart: j in std3_big};
set dart_std3_small := {(i,j) in dart: j in std3_small};

set dart_std4:= {(i,j) in dart: j in std4};
set dart3:= setof {(i1,i2,i3,j1,k1,k2,k3,j2) in e_dart cross e_dart: 
   (j1 = j2) and (i2=k1) and (i3=k2) and (i1=k3)} (i1,j1);

# apex sets
set apex_flat within {(i,j) in dart : j in non_std};
set apex_sup_flat within {(i,j) in dart : j in non_std};
set apex_A within {(i,j) in dart : j in non_std};
set apex4 within {(i,j) in dart: j in non_std};  
set apex5 within {(i,j) in dart : j in non_std};  

# directed edges
set d_edge_225_252 within d_edge;
set d_edge_200_225 within d_edge;

# nodes.
set node_218_252 within node;
set node_236_252 within node_218_252;
set node_218_236 within node_218_252;
set node_200_218 within node;

## SPECIAL SETS OF dartS ##

# parts of darts of opposite nodes of apex_sup_flat:
set apex_sup_flat_pair := 
  setof {(i1,i2,i3,j1,i4,k3,k2,j2) in e_dart cross e_dart: 
  (i1,j1) in apex_sup_flat and (i4,j2) in apex_sup_flat and 
  (i2=k2) and (i3=k3)} (i1,j1,i4,j2);

# darts with opposite at least 2.52 others in [2,2.52].
set dartX :=  apex5 union
   setof{(i1,i2,i3,j) in e_dart: (i3,j) in apex5}(i1,j) union
   setof{(i1,i2,i3,j) in e_dart: (i3,j) in apex5}(i2,j) union
   {(i,j) in dart: j in std4 union std5 union std6};

# darts with opposite at least s8, others in [2,2.52].
set dartY := apex_sup_flat union apex4 union
    setof{(i1,i2,i3,j) in e_dart : (i2,j) in apex4}(i1,j);

# darts with opposite at least 3, others in [2,2.52].
set dart4_diag3 := {(i,j) in dart: j in std4_diag3};
set dart4_diag3_a := dart4_diag3;

set dart_std3_200_218 := setof{(i1,i2,i3,j) in e_dart : 
   i1 in node_200_218 and
   i2 in node_200_218 and
   i3 in node_200_218 and
    j in std3}(i2,j);

# hll means high-low-low

set apex_std3_hll := setof{(i1,i2,i3,j) in e_dart : 
   i1 in node_200_218 and
   i2 in node_218_252 and
   i3 in node_200_218 and
   j in std3}(i2,j);

set apex_std3_lhh := setof{(i1,i2,i3,j) in e_dart : 
   i1 in node_218_252 and
   i2 in node_200_218 and
   i3 in node_218_252 and
   j in std3}(i2,j);


#combined with dart_std3_mini, which does not have to be small!
set dart_std3_small_200_218 := dart_std3_200_218 inter dart_std3_small;

set dart_std3_big_200_218 := dart_std3_200_218 inter dart_std3_big;
set apex_std3_small_hll := apex_std3_hll inter dart_std3_small;

# basic variables
var azim{dart} >= 0, <= pi;
var azim2{dart3} >=0, <= pi;
var azim3{dart3} >=0, <= pi;
var ln{node} >= 0, <= 1;
var rhazim{dart} >=0, <= pi + sol0;
var rhazim2{dart3} >=0, <= pi + sol0;
var rhazim3{dart3} >=0, <= pi + sol0;
var yn{node} >= 2, <= 2.52;
var ye{d_edge} >= 2, <= 3;
var rho{node} >= 1, <= 1 + sol0/pi;
var sol{face} >= 0, <= 4.0*pi;
var tau{face} >= 0, <= tgt;
var y1{dart} >= 2, <=2.52;
var y2{dart} >=2, <=2.52;
var y3{dart} >=2, <=2.52;
var y4{dart3} >=2, <=3;
var y5{dart} >=2, <=3;
var y6{dart} >=2, <=3;
var y8{dart_std4} >= 2, <= 2.52;
var y9{dart_std4} >= 2, <= 2.52;

#report variables
var lnsum;
var ynsum;
var sqdeficit;

## objective
maximize objective:  lnsum;

## equality constraints
lnsum_def: sum{i in node} ln[i]  = lnsum;
ynsum_def: sum{i in node} yn[i] = ynsum;
sqdeficit_def: tgt - sum{j in face} tau[j] = sqdeficit;
azim_sum{i in node}:  sum {(i,j) in dart} azim[i,j] = 2.0*pi;
rhazim_sum{i in node}:  sum {(i,j) in dart} rhazim[i,j] = 2.0*pi*rho[i];
sol_sum{j in face}: sum{(i,j) in dart} (azim[i,j] - pi) = sol[j] - 2.0*pi;
tau_sum{j in face}: sum{(i,j) in dart} (rhazim[i,j] - pi -sol0) = tau[j] - 2.0*(pi+sol0);
ln_def{i in node}: ln[i] = (2.52 - yn[i])/0.52;
rho_def{i in node}: rho[i] = (1 + sol0/pi) - ln[i] * sol0/pi;
edge_sym{(i1,j1,i2,j2) in edge}: ye[i1,j1] = ye[i2,j2];
y1_def{(i3,i1,i2,j) in e_dart}: y1[i1,j] = yn[i1];
y2_def{(i3,i1,i2,j) in e_dart}: y2[i1,j] = yn[i2];
y3_def{(i3,i1,i2,j) in e_dart}: y3[i1,j] = yn[i3];
y4_def{(i3,i1,i2,j) in e_dart :  (i1,j) in dart3}: y4[i1,j] = ye[i2,j];
y5_def{(i3,i1,i2,j) in e_dart}: y5[i1,j] = ye[i3,j];
y6_def{(i3,i1,i2,j) in e_dart}: y6[i1,j] = ye[i1,j];
y9_def{(i3,i1,i2,j) in e_dart : (i1,j) in dart_std4 }: y9[i1,j] = ye[i2,j];
y8_def{(i3,i1,i2,j) in e_dart: (i1,j) in dart_std4}: y8[i1,j] = y5[i3,j];
azim2c{(i1,i2,i3,j) in e_dart : (i2,j) in dart3}: azim2[i2,j] = azim[i3,j];
azim3c{(i1,i2,i3,j) in e_dart : (i2,j) in dart3}: azim3[i2,j] = azim[i1,j];
rhazim2c{(i1,i2,i3,j) in e_dart : (i2,j) in dart3}: rhazim2[i2,j] = rhazim[i3,j];
rhazim3c{(i1,i2,i3,j) in e_dart : (i2,j) in dart3}: rhazim3[i2,j] = rhazim[i1,j];

## inequality constraints
main: sum{i in node} ln[i] >= 12;
RHA{(i,j) in dart}: rhazim[i,j] >= azim[i,j]*1.0;
RHB{(i,j) in dart}: rhazim[i,j] <= azim[i,j]*(1+sol0/pi);
RHBLO{(i,j) in dart: i in node_200_218}: rhazim[i,j] <= azim[i,j]*rho218;
RHBHI{(i,j) in dart: i in node_218_252}: rhazim[i,j] >= azim[i,j]*rho218;

## definitional inequalities
yy1 {(i,j) in dart_std3_big}:   y4[i,j]+y5[i,j]+y6[i,j] >= 6.25;
yy2 {(i,j) in dart_std3_small}:   y4[i,j]+y5[i,j]+y6[i,j] <= 6.25;
yy3 {i in node_218_252}: yn[i] >= 2.18;
yy4 {i in node_200_218}: yn[i] <= 2.18;
yy5 {i in node_236_252}: yn[i] >= 2.36;
yy6 {i in node_218_236}: yn[i] <= 2.36;
yy7 {i in node_218_236}: yn[i] >= 2.18;
yy8 {(i,j) in d_edge_225_252}: ye[i,j] >= 2.25;
yy9 {(i,j) in d_edge_200_225}: ye[i,j] <= 2.25;

# y bounds.
yy10 {(i,j) in dart : j in std}: ye[i,j] <= 2.52;
yy11 {(i,j) in apex_flat}: y4[i,j] >= 2.52;
yy12 {(i,j) in apex_sup_flat}: y4[i,j] >= sqrt8;
yy13 {(i,j) in apex_flat union apex_sup_flat}: y5[i,j] <= 2.52;
yy14 {(i,j) in apex_flat union apex_sup_flat}: y6[i,j] <= 2.52;
yy15 {(i,j) in dart3 diff apex_sup_flat}: y4[i,j] <= sqrt8;
yy16 {(i,j) in apex_A}: y4[i,j] <= 2.52; # others redun. via apex_flat
# {(i,j) in apex_sup_flat}: y4[i,j] <= 3; # redundant via ye.
# apex4 apex5: covered by neighbors unless there are 2.

# tau tame table D inequality (Main Estimate)

tau3{j in std3}: tau[j] >= 0;
tau4{j in std4}: tau[j] >= 0.206;
tau5{j in std5}: tau[j] >= 0.4819;
tau6{j in std6}: tau[j] >= 0.7578;

## XXD to HERE.

# secondary estimates:
tauB5h 'ID[]' {(i,j) in apex5}: tau[j] >= 0.6548; # = tame table D[4,1]
tauB4h 'ID[9620775909]' {(i,j) in apex4}: tau[j] >= 0.492;
tau5h 'ID[]' {j in std5 inter std56_flat_free}: tau[j] >= 0.751;
tau6h 'ID[]' {j in std6 inter std56_flat_free}: tau[j] >= 0.91;

perimZ 'ID[5691615370]' {(i1,i2,i3,j) in e_dart : j in std4_diag3}:
  y5[i1,j] + y6[i1,j] + y5[i3,j] + y6[i3,j] >= 8.472;

tausf3 'ID[5451229371]'  {(i1,j1,i2,j2) in apex_sup_flat_pair}:
 tau[j1]+tau[j2]  - 0.24
    -0.14132*(y1[i1,j1]+ y2[i1,j1] + y3[i1,j1] + y1[i2,j2] - 8)
    -0.38*(y5[i1,j1]+y6[i1,j1]+y5[i2,j2]+y6[i2,j2] -8) >= 0;

yapex_sup_flat 'ID[8673686234]' {(i1,j1,i2,j2) in apex_sup_flat_pair}:
   (y5[i1,j1]+y6[i1,j1]+y5[i2,j2]+y6[i2,j2]-8) >= 2.75*(y4[i1,j1]-sqrt8);


# this one based on fact that crossdiag of apex_sup_flat is longer than diag.
# y4[i1,j1] is the diag, which is shorter than the cross diag. 
# By monotonicity of dih in opposite edge length, this may be substituted in.
# checked 2010-06-23.
crossdiag 'ID[1085358243]+' 
   {(i1,i,i3,j1,k1,k2,k3,j2) in e_dart cross e_dart :
     i = k3 and i3 = k2 and (i1,j1,k1,j2) in apex_sup_flat_pair}:
  (azim[i,j1]+azim[i,j2]) - 1.903 - 0.4*(y1[i,j1] - 2)
  +0.49688*(y2[i,j2]+y3[i,j1]+y5[i,j1]+y6[i,j2]-8)
   -(y4[i1,j1]-sqrt8) >= 0;


# final dart sets.

set apex_flat_hll := setof {(i1,i,i3,j) in e_dart : i1 in node_200_218 and i in node_218_252 and  i3 in node_200_218 and (i,j) in apex_flat} (i,j);

set dart_mll_w := setof  {(i,i2,i3,j) in e_dart : (i2,j) in d_edge_225_252 and (i,j) in apex_std3_hll and i in node_218_236} (i,j);

set dart_mll_n := setof {(i,i2,i3,j) in e_dart : (i2,j) in d_edge_200_225 and (i,j) in apex_std3_hll and i in node_218_236} (i,j);

set dart_Hll_n :=  setof {(i,i2,i3,j) in e_dart : (i2,j) in d_edge_200_225 and (i,j) in apex_std3_hll and i in node_236_252} (i,j);

set dart_Hll_w :=  setof {(i,i2,i3,j) in e_dart : (i2,j) in d_edge_225_252 and (i,j) in apex_std3_hll and i in node_236_252} (i,j);

set apexf4 := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex4} (i2,j);
set apexff4 := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex4} (i3,j);
set apexf5 := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex5} (i2,j);
set apexff5 := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex5} (i3,j);
set apexfA := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex_A} (i2,j);
set apexffA := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex_A} (i3,j);

# added Aug 1, 2010.  low and wide.

set dart_std3_lw  :=  setof   {(i,i2,i3,j) in e_dart : (i2,j) in d_edge_225_252 and (i,j) in dart_std3_big and i in node_200_218}  (i,j);

# added Aug 2, 2010, corrected Aug 3, 2010.

set dart_std3_mini := dart_std3_small_200_218 union 
   setof {(i1,i2,i3,j) in e_dart: (i1,j) in d_edge_200_225 
     and      (i2,j) in d_edge_200_225 and (i3,j) in d_edge_200_225 
     and i1 in node_200_218 
     and i2 in node_200_218 and i3 in node_200_218 } (i1,j);

set apex_flat_l := {(i,j) in apex_flat : i in node_200_218 };

# Aug 3, 2010

set apex_std3_lll_xww := 
  setof {(i,i2,i3,j) in e_dart : (i,j) in d_edge_225_252 
    and (i3,j) in d_edge_225_252
    and (i,j) in dart_std3_200_218 } (i,j);

set apex_std3_lll_wxx := 
    setof {(i,i2,i3,j) in e_dart : (i2,j) in d_edge_225_252 
    and (i,j) in dart_std3_200_218 } (i,j);

#set apex_std3_mll_nwn :=
#  setof {(i,i2,i3,j) in e_dart : (i,j) in d_edge_200_225
#    and (i2,j) in d_edge_200_225  
#    and (i3,j) in d_edge_225_252
#    and (i,j) in dart_mll_n  } (i,j);

# Aug 5, 2010.

set apex_flat_h :=  {(i,j) in apex_flat : i in node_218_252 };


# PUT auto generated body here.




 
