/* AMPL model for the Kepler conjecture
File created May 8, 2009
Revised June 20, 2009
Thomas C. Hales
*/

# data file supplies param: graphID, CVERTEX, CFACE, set: EDGE EDART ITRIANGLE IQUAD IPENT IHEX

param graphID;
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
set EDGE within DART cross DART := setof{(i1,i2,i3,j1) in EDART,(i0,i3,i2,j2) in EDART}(i2,j1,i3,j2);

set faceof{i in IVERTEX} := setof {  (i,j) in DART}(j);
set vertexof{j in IFACE}:= setof { (i,j) in DART} (i);
set ITRIANGLE;
set IQUAD;
#set BQUAD;
set IPENT;
set IHEX;
set SHEX;
set EDART3:= {(i1,i2,i3,j) in EDART: j in ITRIANGLE};
set EDARTX:= {(i1,i2,i3,j) in EDART: j not in ITRIANGLE};



# variables
var azim{DART} >= 0, <= pi;
var ln{IVERTEX} >= 0, <= 1;
var rhazim{DART} >=0, <= pi + delta0;
var yn{IVERTEX} >= 2, <= 2.52;
var ye{DEDGE} >= 2, <= 2.52;
var rho{IVERTEX} >= 1, <= 1 + delta0/pi;
var sol{IFACE} >= 0, <= 4.0*pi;
var tau{IFACE} >= 0, <= tgt;
var y1{EDART};
var y2{EDART};
var y3{EDART};
var y4{EDART3};
var y5{EDART};
var y6{EDART};
var lnsum;
var ynsum;

## objective
#maximize objective:  sum {i in IVERTEX} yn[i];
#maximize obj: azim[12,12];
maximize objective:  lnsum;


## equality constraints
s.t. lnsum_def: sum{i in IVERTEX} ln[i]  = lnsum;
s.t. ynsum_def: sum{i in IVERTEX} yn[i] = ynsum;
s.t. azim_sum{i in IVERTEX}:  sum {(i,j) in DART} azim[i,j] = 2.0*pi;
s.t. rhazim_sum{i in IVERTEX}:  sum {(i,j) in DART} rhazim[i,j] = 2.0*pi*rho[i];
s.t. sol_sum{j in IFACE}: sum{(i,j) in DART} (azim[i,j] - pi) = sol[j] - 2.0*pi;
s.t. tau_sum{j in IFACE}: sum{(i,j) in DART} (rhazim[i,j] - pi -delta0) = tau[j] - 2.0*(pi+delta0);
s.t. ln_def{i in IVERTEX}: ln[i] = (2.52 - yn[i])/0.52;
s.t. rho_def{i in IVERTEX}: rho[i] = (1 + delta0/pi) - ln[i] * delta0/pi;
s.t. edge{(i1,j1,i2,j2) in EDGE}: ye[i1,j1] = ye[i2,j2];
s.t. y1_def{(i3,i1,i2,j) in EDART} : y1[i3,i1,i2,j] = yn[i1];
s.t. y2_def{(i3,i1,i2,j) in EDART} : y2[i3,i1,i2,j] = yn[i2];
s.t. y3_def{(i3,i1,i2,j) in EDART} : y3[i3,i1,i2,j] = yn[i3];
s.t. y4_def{(i3,i1,i2,j) in EDART3} : y4[i3,i1,i2,j] = ye[i2,j];
s.t. y5_def{(i3,i1,i2,j) in EDART} : y5[i3,i1,i2,j] = ye[i3,j];
s.t. y6_def{(i3,i1,i2,j) in EDART} : y6[i3,i1,i2,j] = ye[i1,j];

# inequality constraints
s.t. main: sum{i in IVERTEX} ln[i] >= 12;
s.t. azmin{(i,j) in DART : j in ITRIANGLE} : azim[i,j] >= 0.852;
s.t. azmax{(i,j) in DART : j in ITRIANGLE} : azim[i,j] <= 1.893;
s.t. RHA{(i,j) in DART} : azim[i,j] <= rhazim[i,j];
s.t. RHB{(i,j) in DART} : rhazim[i,j] <= azim[i,j]*(1+delta0/pi);

s.t. solyA{(i1,i2,i3,j) in EDART3} : sol[j] - 0.55125 - 0.196*(y4[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-6) + 0.38*(y1[i1,i2,i3,j]+y2[i1,i2,i3,j]+y3[i1,i2,i3,j]-6) >= 0;
s.t. solyB{(i1,i2,i3,j) in EDART3} : -sol[j] + 0.5513 + 0.3232*(y4[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-6) - 0.151*(y1[i1,i2,i3,j]+y2[i1,i2,i3,j]+y3[i1,i2,i3,j]-6) >= 0;

s.t.  azminA{(i1,i2,i3,j) in EDART3}: azim[i2,j] - 1.2308 
  + 0.3639*(y2[i1,i2,i3,j]+y3[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-8) - 0.235*(y1[i1,i2,i3,j]-2) - 0.685*(y4[i1,i2,i3,j]-2) >= 0;
s.t.  azmaxA{(i1,i2,i3,j) in EDART3}: -azim[i2,j] + 1.231 
  - 0.152*(y2[i1,i2,i3,j]+y3[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-8) + 0.5*(y1[i1,i2,i3,j]-2) + 0.773*(y4[i1,i2,i3,j]-2) >= 0;
s.t. azminX{(i1,i2,i3,j) in EDARTX}: azim[i2,j] - 1.629 
  + 0.402*(y2[i1,i2,i3,j]+y3[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-8) - 0.315*(y1[i1,i2,i3,j]-2)  >= 0;

s.t.   rhazminA{(i1,i2,i3,j) in EDART3}: rhazim[i2,j] - 1.2308 
  + 0.3639*(y2[i1,i2,i3,j]+y3[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-8) - 0.6*(y1[i1,i2,i3,j]-2) - 0.685*(y4[i1,i2,i3,j]-2) >= 0;

# tau inequality
s.t. tau3{j in ITRIANGLE}: tau[j] >= 0;
s.t. tau4{j in IQUAD}: tau[j] >= 0.206;
#tau4B{j in IQUAD}: tau[j] >= 0.256;
s.t. tau5{j in IPENT}: tau[j] >= 0.483;
#s.t. tau5h{j in IPENT}: tau[j] >= 0.751;
tau6{j in IHEX}: tau[j] >= 0.76;
#tau6h{j in IHEX}: tau[j] >= 0.91;

s.t. tau_azim3A{(i,j) in DART : j in ITRIANGLE}: tau[j]+0.626*azim[i,j] - 0.77 >= 0;
s.t. tau_azim3B{(i,j) in DART : j in ITRIANGLE}: tau[j]-0.259*azim[i,j] + 0.32 >= 0;
s.t. tau_azim3C{(i,j) in DART : j in ITRIANGLE}: tau[j]-0.507*azim[i,j] + 0.724 >= 0;
s.t. tau_azim3D{(i1,i2,i3,j) in EDART3}: tau[j] + 0.001 -0.18*(y1[i1,i2,i3,j]+y2[i1,i2,i3,j]+y3[i1,i2,i3,j]-6) - 0.125*(y4[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-6) >= 0;

s.t. tau_azim4A{(i,j) in DART : j in IQUAD}: tau[j] + 4.72*azim[i,j] - 6.248 >= 0;
s.t. tau_azim4B{(i,j) in DART : j in IQUAD}: tau[j] + 0.972*azim[i,j] - 1.707 >= 0;
s.t. tau_azim4C{(i,j) in DART : j in IQUAD}: tau[j] + 0.7573*azim[i,j] - 1.4333 >= 0;
s.t. tau_azim4D{(i,j) in DART : j in IQUAD}: tau[j] + 0.453*azim[i,j] + 0.777 >= 0;

#superhex inequality (branch and bound case)
tau6h{j in SHEX}: tau[j] >= 0.91;




solve;
#display graphID;
display lnsum;
#display ynsum;
#display yn;
#display ye;
#display azim;
#display rhazim;
#display sol;
#display solve_result_num;
#display solve_result;












