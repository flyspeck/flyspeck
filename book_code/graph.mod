/* AMPL model for the Kepler conjecture
File created May 8, 2009
Thomas C. Hales
*/


param pi;

param CVERTEX >= 13, <= 14;   # card of vertices in the hypermap
param CFACE >= 0;   # card of faces in the hypermap

set IVERTEX = 1..CVERTEX;

set IFACE = 1..CFACE;
set FACE{IFACE} circular;

set ITRIANGLE := {j in IFACE : card(FACE[j]) = 3};
set IQUAD := {j in IFACE: card(FACE[j]) = 4};
set IEXCEPT:= IFACE diff (ITRIANGLE union IQUAD);

## darts and directed edges
# directed edge (i,j) is identified with (i,i2) i2 = nextw(i,FACE[j]);
set DART := {i in IVERTEX , j in IFACE: i in FACE[j]};
set DEDGE := DART;


## variable declarations
var azim{DART} >= 0, <= 2.0*pi;
var area{IFACE} >= 0, <= 4.0*pi;
var sqface{IFACE};  # squander face
var yv{IVERTEX} >= 2, <= 2.52;
var fm{IVERTEX} >= 0, <= 1;
var ye{DEDGE} >= 2, <= 2.52;

#var alpha_fm{DART} >= 0, <= 2.0*pi;  # product of azim[i,j]*fm[i]
#var local_area{DART} >= 0, <= 4.0*pi; 

## objective
maximize objective:  sum {i in IVERTEX} fm[i];

## constraints
subject to fm_def{i in IVERTEX}: fm[i] =  (1 - (yv[i]/2.52 - 1) );
subject to vertex_sum{i in IVERTEX}:  sum {(i,j) in DART} azim[i,j] = 2.0*pi;
subject to area_def{j in IFACE}: sum{(i,j) in DART} (azim[i,j] - pi) = area[j] - 2.0*pi;
#subject to area_local{j in IFACE}: sum{(i,j) in DART} local_area[i,j] <= area[j];
subject to sqface_def{j in IFACE}: 


param dihminp;
param dihmaxp;
param dihminq;
param dihmaxq;
param target;
param cc2Pi;
param SFACE := 3..8;
param SQFACE[SFACE];

subject to azim_dihminp {(i,j) in DART: j in ITRIANGLE}:  azim[i,j] >= dihminp;
subject to azim_dihmaxp {(i,j) in DART: j in ITRIANGLE}:  azim[i,j] <= dihmaxp;
subject to azim_dihminq {(i,j) in DART: j in IQUAD union IEXCEPT}:  azim[i,j] >= dihminq;
subject to azim_dihmaxp {(i,j) in DART: j in IQUAD union IEXCEPT}:  azim[i,j] <= dihmaxq;
subject to face_sq{j in IQUAD union IEXCEPT} sqface[j] >= SQFACE[card(FACE[j])];
subject to target_def: sum{j in IFACE} sqface[j] = target + cc2Pi*(12.0 -sum {i in IVERTEX} fm[i]);

# add squander target constraints.
# add area inequalities
# add if degree is 2 then yv=2.0;
# give parameter definitions.












