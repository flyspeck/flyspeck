/* AMPL model for the Kepler conjecture
File created May 8, 2009
Revised June 20, 2009
Thomas C. Hales
*/

# data file supplies param: CVERTEX, CFACE, set: EDART


param pi := 3.1415926535897932;
param delta0 := 0.5512855984325308;
param tgt := 1.54065864570856;


param CVERTEX 'number of vertices' >= 1, <= 14; 
param CFACE 'number of faces' >= 0; 


# directed edge (i,j) with its tail i.
# edart (i1,i2,i3,j), s.t. f(i1,j) = (i2,j), f(i2,j) = (i3,j)
set IVERTEX := 1..CVERTEX;
set IFACE := 1..CFACE;
set EDART 'extended dart' within IVERTEX cross IVERTEX cross IVERTEX cross IFACE;
set DART := setof {(i1,i2,i3,j) in EDART} (i1,j);
set DEDGE := DART;

set faceof{i in IVERTEX} := setof {  (i,j) in DART}(j);
set vertexof{j in IFACE}:= setof { (i,j) in DART} (i);
set ITRIANGLE := {j in IFACE : card(vertexof[j]) = 3};
set IQUAD := {j in IFACE: card(vertexof[j]) = 4};
set IPENT := {j in IFACE: card(vertexof[j]) = 5};
set IHEX := {j in IFACE: card(vertexof[j]) = 6};
set IEXCEPT:= {j in IFACE: card(vertexof[j]) > 4};
