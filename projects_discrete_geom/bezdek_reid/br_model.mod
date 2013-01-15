/* ========================================================================== */
/* FLYSPECK - BOOK FORMALIZATION                                              */
/*                                                                            */
/* Bezdek Reid calculation   */
/* Author: Thomas C. Hales                                                    */
/* Date: 2013-01-13                                                          */
/* ========================================================================== */

/* adapted from contact.mod used in Fejes Toth conjecture */

# 

param hypermapID;
param pi := 3.1415926535897932;
param delta0 := 0.5512855984325308;
param dih0 := 1.230959417340774682;
param CVERTEX := 12;
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
set IHEPT;
set IOCT;
set STANDARD := ITRIANGLE union IQUAD union IPENT union IHEX union IHEPT union IOCT; # standard regions.
set IDART3:= {(i,j) in DART: j in ITRIANGLE};
set IDART4:= {(i,j) in DART: j in IQUAD};
set ALLTRI:= setof {(i1,i2,i3,j1,k1,k2,k3,j2) in EDART cross EDART: (j1 = j2) and (i2=k1) and (i3=k2) and (i1=k3)} (i1,j1);

#basic variables
var optival;
var azim{DART} >= 0, <= 2*pi;
var sol{STANDARD} >= 0, <= 4*pi;

## objective
minimize objective:  optival;

## equality constraints
optsum: - optival + sum {j in FACE} sol[j] = 4*pi;
azim_sum{i in IVERTEX}:  sum {(i,j) in DART} azim[i,j] = 2.0*pi;
sol_sum{j in FACE}: sum{(i,j) in DART} (azim[i,j] - pi) <= sol[j] - 2.0*pi;

## error constraint: should be zero.
error_bound: optival <= 0.5;

# trivial bounds on solid angles from Lexell and Delaunay triangulation.
sol3{j in ITRIANGLE}: sol[j] >= delta0;
sol4{j in IQUAD}: sol[j] >= 2.0 * delta0;
sol5{j in IPENT}: sol[j] >= 3.0 * delta0;
sol6{j in IHEX}: sol[j] >= 4.0 * delta0; 
sol7{j in IHEX}: sol[j] >= 5.0 * delta0; 
sol8{j in IHEX}: sol[j] >= 6.0 * delta0; 

# azim bounds #
azim3eq {(i,j) in IDART3}: azim[i,j] = dih0;
azimlb {(i,j) in DART :  j in STANDARD diff ITRIANGLE} : azim[i,j] >= dih0;

# rhombus conditions
# 2 Dihedral[2,2,2,2,2,2];
azim4ub {(i,j) in IDART4}: azim[i,j] <= 2.0 * dih0;
azim4op {(i1,i2,i3,j) in EDART : (i2,j) in IDART4} : azim[i1,j]= azim[i3,j];

solve;
display hypermapID;
display optival;
display azim;

