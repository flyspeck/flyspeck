/* AMPL model for the Kepler conjecture
File created May 8, 2009
Revised June 20, 2009
Thomas C. Hales
copied from graph0.mod on June 30.
Deprecated approach.
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

set ITRIANGLE;
set IQUAD;
set IPENT;
set IHEX;
set EDART3:= {(i1,i2,i3,j) in EDART: j in ITRIANGLE};
set EDARTX:= {(i1,i2,i3,j) in EDART: j not in ITRIANGLE};

# branch sets
set SQUAD within IQUAD;
set SPENT within IPENT;
set SHEX within IHEX;
set FLAT within {(i,j) in DART : j not in ITRIANGLE};
set APIECE within {(i,j) in DART : j in IPENT};
set FA := FLAT union APIECE;
set BIGPIECE within {(i,j) in FLAT : j in IPENT union IHEX};
set BIGTRI within ITRIANGLE;
set SMALLTRI within ITRIANGLE;
set HIGHVERTEX within IVERTEX;
set LOWVERTEX within IVERTEX;

# basic variables
var azim{DART} >= 0, <= pi;
var ln{IVERTEX} >= 0, <= 1;
var rhazim{DART} >=0, <= pi + delta0;
var yn{IVERTEX} >= 2, <= 2.52;
var ye{DEDGE} >= 2, <= 2.52;
var rho{IVERTEX} >= 1, <= 1 + delta0/pi;
var sol{IFACE} >= 0, <= 4.0*pi;
var tau{IFACE} >= 0, <= tgt;
var y1{EDART} >= 0, <=2.52;
var y2{EDART} >=0, <=2.52;
var y3{EDART} >=0, <=2.52;
var y4{EDART3} >=0, <=2.52;
var y5{EDART} >=0, <=2.52;
var y6{EDART} >=0, <=2.52;


#report variables
var lnsum;
var ynsum;

#branch variables FLAT and APIECE
var diag{FLAT} >=0, <= 2.0*2.52;
var y1FA{FA} >=0, <= 2.52;
var y2FA{FA} >=0, <= 2.52;
var y3FA{FA} >=0, <= 2.52;
var y4FA{FA} >=0;
var y5FA{FA} >=0;
var y6FA{FA} >=0;
var azim1FA{FA} >=0, <= pi;
var azim2FA{FA} >=0, <= pi;
var azim3FA{FA} >=0, <= pi;
var rhazim1FA{FA} >=0, <= pi + delta0;
var rhazim2FA{FA} >=0, <= pi + delta0;
var rhazim3FA{FA} >=0, <= pi + delta0;
var solFA{FA} >=0, <= 4.0*pi;
var tauFA{FA} >=0, <= tgt;

#branch variables BIGPIECE
var solBIG{BIGPIECE} >=0, <= 4.0*pi;
var tauBIG{BIGPIECE} >=0, <= 4.0*pi;
var y1R{BIGPIECE} >=0, <= 2.52;
var y2R{BIGPIECE} >=0, <= 2.52;
var y3R{BIGPIECE} >=0, <= 2.52;
var y5R{BIGPIECE} >=0, <= 2.0*2.52;
var y6R{BIGPIECE} >=0, <= 2.52;
var y1P{BIGPIECE} >=0, <= 2.52;
var y2P{BIGPIECE} >=0, <= 2.52;
var y3P{BIGPIECE} >=0, <= 2.52;
var y5P{BIGPIECE} >=0, <= 2.52;
var y6P{BIGPIECE} >=0, <= 2.0*2.52;
var azimR{BIGPIECE} >=0, <= pi;
var azimP{BIGPIECE} >=0, <= pi;
var rhazimR{BIGPIECE} >=0, <= pi + delta0;
var rhazimP{BIGPIECE} >=0, <= pi + delta0;

## objective
maximize objective:  lnsum;

## equality constraints
lnsum_def: sum{i in IVERTEX} ln[i]  = lnsum;
ynsum_def: sum{i in IVERTEX} yn[i] = ynsum;
azim_sum{i in IVERTEX}:  sum {(i,j) in DART} azim[i,j] = 2.0*pi;
rhazim_sum{i in IVERTEX}:  sum {(i,j) in DART} rhazim[i,j] = 2.0*pi*rho[i];
sol_sum{j in IFACE}: sum{(i,j) in DART} (azim[i,j] - pi) = sol[j] - 2.0*pi;
tau_sum{j in IFACE}: sum{(i,j) in DART} (rhazim[i,j] - pi -delta0) = tau[j] - 2.0*(pi+delta0);
ln_def{i in IVERTEX}: ln[i] = (2.52 - yn[i])/0.52;
rho_def{i in IVERTEX}: rho[i] = (1 + delta0/pi) - ln[i] * delta0/pi;
edge{(i1,j1,i2,j2) in EDGE}: ye[i1,j1] = ye[i2,j2];
y1_def{(i3,i1,i2,j) in EDART} : y1[i3,i1,i2,j] = yn[i1];
y2_def{(i3,i1,i2,j) in EDART} : y2[i3,i1,i2,j] = yn[i2];
y3_def{(i3,i1,i2,j) in EDART} : y3[i3,i1,i2,j] = yn[i3];
y4_def{(i3,i1,i2,j) in EDART3} : y4[i3,i1,i2,j] = ye[i2,j];
y5_def{(i3,i1,i2,j) in EDART} : y5[i3,i1,i2,j] = ye[i3,j];
y6_def{(i3,i1,i2,j) in EDART} : y6[i3,i1,i2,j] = ye[i1,j];
diag_quad{(i1,i2,i3,j) in EDART: j in IQUAD}: diag[i1,j] = diag[i3,j];

#equality FLAT branch
y1F_def{(i,j) in FLAT} : y1FA[i,j] = yn[i];
y2F_def{(i3,i1,i2,j) in EDART : (i1,j) in FLAT}: y2FA[i1,j] = yn[i2];
y3F_def{(i3,i1,i2,j) in EDART : (i1,j) in FLAT}: y3FA[i1,j] = yn[i3];
y4F_def{(i,j) in FLAT}: y4FA[i,j] = diag[i,j];
y5F_def{(i1,i2,i3,j) in EDART : (i2,j) in FLAT}: y5FA[i2,j] = ye[i1,j];
y6F_def{(i1,i2,i3,j) in EDART: (i2,j) in FLAT}: y6FA[i2,j] = ye[i2,j];
azimF_def{(i,j) in FLAT}: azim1FA[i,j] = azim[i,j];
solF_def{(i,j) in FLAT}: solFA[i,j] = azim1FA[i,j] + azim2FA[i,j] + azim3FA[i,j] - pi;
tauF_def{(i,j) in FLAT}: tauFA[i,j] = rhazim1FA[i,j] + rhazim2FA[i,j] + rhazim3FA[i,j] - (pi+delta0);

#equality FLAT-FLAT
azimFF_sum{(i1,i2,i3,j) in EDART: (i1,j) in FLAT and  j in IQUAD and (i3,j) in FLAT}:
  azim2FA[i1,j] + azim3FA[i3,j] = azim[i2,j];
rhazimFF_sum{(i1,i2,i3,j) in EDART: (i1,j) in FLAT and  j in IQUAD and (i3,j) in FLAT}:
  rhazim2FA[i1,j] + rhazim3FA[i3,j] = rhazim[i2,j];

#equality FLAT-BIGPIECE
azimFR_sum{(i1,i,i3,j) in EDART: (i,j) in FLAT inter BIGPIECE}:
  azim2FA[i,j] + azimR[i,j] = azim[i3,j];
azimFP_sum{(i1,i,i3,j) in EDART: (i,j) in FLAT inter BIGPIECE}:
  azim3FA[i,j] + azimP[i,j] = azim[i1,j];
rhazimFR_sum{(i1,i,i3,j) in EDART: (i,j) in FLAT inter BIGPIECE}:
  rhazim2FA[i,j] + rhazimR[i,j] = rhazim[i3,j];
rhazimFP_sum{(i1,i,i3,j) in EDART: (i,j) in FLAT inter BIGPIECE}:
  rhazim3FA[i,j] + rhazimP[i,j] = rhazim[i1,j];

#equality FLAT-APIECE
y1A_def{(i,j) in APIECE}: y1FA[i,j] = yn[i];
y2A_def{(i1,i2,i3,j) in EDART: (i1,j) in APIECE}: y2FA[i1,j] = yn[i3];
y3A_def{(i1,i2,i3,j) in EDART: (i3,j) in APIECE}: y3FA[i3,j] = yn[i1];
y4A_def{(i1,i2,i3,j) in EDART: (i1,j) in APIECE}: y4FA[i1,j] = ye[i3,j];
y5A_def{(i1,i2,i3,j) in EDART: (i3,j) in APIECE}: y5FA[i3,j] = diag[i2,j];
y6A_def{(i1,i2,i3,j) in EDART: (i1,j) in APIECE}: y6FA[i1,j]= diag[i2,j];
solA_def{(i,j) in APIECE}: solFA[i,j] = azim1FA[i,j]+azim2FA[i,j]+azim3FA[i,j] - pi;
tauA_def{(i,j) in APIECE}: tauFA[i,j] = rhazim1FA[i,j]+rhazim2FA[i,j]+rhazim3FA[i,j] - (pi+delta0);
azim1AF_sum{(i1,i2,i3,j) in EDART : (i1,j) in FLAT and (i2,j) in APIECE and (i3,j) in FLAT}:
  azim2FA[i1,j]+azim1FA[i2,j]+azim3FA[i3,j]=azim[i2,j];
rhazim1AF_sum{(i1,i2,i3,j) in EDART : (i1,j) in FLAT and (i2,j) in APIECE and (i3,j) in FLAT}:
  rhazim2FA[i1,j]+rhazim1FA[i2,j]+rhazim3FA[i3,j]=rhazim[i2,j];
azim2AF_sum{(i1,i2,i3,j) in EDART : (i1,j) in APIECE and (i2,j) in FLAT}:
  azim2FA[i1,j] + azim2FA[i2,j] = azim[i3,j];
rhazim2AF_sum{(i1,i2,i3,j) in EDART : (i1,j) in APIECE and (i2,j) in FLAT}:
  rhazim2FA[i1,j] + rhazim2FA[i2,j] = rhazim[i3,j];
azim3AF_sum{(i1,i2,i3,j) in EDART : (i3,j) in APIECE and (i2,j) in FLAT}:
  azim3FA[i2,j] + azim3FA[i3,j] = azim[i1,j];
rhazim3AF_sum{(i1,i2,i3,j) in EDART : (i3,j) in APIECE and (i2,j) in FLAT}:
  rhazim3FA[i2,j] + rhazim3FA[i3,j] = rhazim[i1,j];

#equality BIGPIECE.
solB{(i,j) in BIGPIECE}: solFA[i,j]+solBIG[i,j] = sol[j];
tauB{(i,j) in BIGPIECE}: tauFA[i,j]+tauBIG[i,j] = tau[j];
y1R_def{(i,j) in BIGPIECE}: y1R[i,j] = y2FA[i,j];
y2R_def{(i1,i2,i3,j) in EDART: (i1,j) in BIGPIECE}: y2R[i1,j] = yn[i3];
y3R_def{(i,j) in BIGPIECE}: y3R[i,j] = y3FA[i,j];
y5R_def{(i,j) in BIGPIECE}: y5R[i,j] = diag[i,j];
y6R_def{(i1,i2,i3,j) in EDART: (i2,j) in BIGPIECE}: y6R[i2,j] = ye[i3,j];

y1P_def{(i,j) in BIGPIECE}: y1P[i,j] = y3FA[i,j];
y2P_def{(i,j) in BIGPIECE}: y2P[i,j] = y2FA[i,j];
y3P_def{(i1,i2,i3,j) in EDART: (i3,j) in BIGPIECE}: y3P[i3,j] = yn[i1];
y5P_def{(i1,i2,i3,j)in EDART: (i3,j) in BIGPIECE}: y5P[i3,j] = ye[i1,j];
y6P_def{(i,j) in BIGPIECE}: y6P[i,j] = diag[i,j];

## inequality constraints
main: sum{i in IVERTEX} ln[i] >= 12;
azmin{(i,j) in DART : j in ITRIANGLE} : azim[i,j] >= 0.852;
azmax{(i,j) in DART : j in ITRIANGLE} : azim[i,j] <= 1.893;
RHA{(i,j) in DART} : azim[i,j] <= rhazim[i,j];
RHB{(i,j) in DART} : rhazim[i,j] <= azim[i,j]*(1+delta0/pi);

solyA{(i1,i2,i3,j) in EDART3} : sol[j] - 0.55125 - 0.196*(y4[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-6) + 0.38*(y1[i1,i2,i3,j]+y2[i1,i2,i3,j]+y3[i1,i2,i3,j]-6) >= 0;
solyB{(i1,i2,i3,j) in EDART3} : -sol[j] + 0.5513 + 0.3232*(y4[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-6) - 0.151*(y1[i1,i2,i3,j]+y2[i1,i2,i3,j]+y3[i1,i2,i3,j]-6) >= 0;

azminA{(i1,i2,i3,j) in EDART3}: azim[i2,j] - 1.2308 
  + 0.3639*(y2[i1,i2,i3,j]+y3[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-8) - 0.235*(y1[i1,i2,i3,j]-2) - 0.685*(y4[i1,i2,i3,j]-2) >= 0;
azmaxA{(i1,i2,i3,j) in EDART3}: -azim[i2,j] + 1.231 
  - 0.152*(y2[i1,i2,i3,j]+y3[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-8) + 0.5*(y1[i1,i2,i3,j]-2) + 0.773*(y4[i1,i2,i3,j]-2) >= 0;
azminX{(i1,i2,i3,j) in EDARTX}: azim[i2,j] - 1.629 
  + 0.402*(y2[i1,i2,i3,j]+y3[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-8) - 0.315*(y1[i1,i2,i3,j]-2)  >= 0;

rhazminA{(i1,i2,i3,j) in EDART3}: rhazim[i2,j] - 1.2308 
  + 0.3639*(y2[i1,i2,i3,j]+y3[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-8) - 0.6*(y1[i1,i2,i3,j]-2) - 0.685*(y4[i1,i2,i3,j]-2) >= 0;

# tau inequality
tau3{j in ITRIANGLE}: tau[j] >= 0;
tau4{j in IQUAD}: tau[j] >= 0.206;
tau5{j in IPENT}: tau[j] >= 0.483;
tau6{j in IHEX}: tau[j] >= 0.76;
#tau6h{j in IHEX}: tau[j] >= 0.91;

tau_azim3A{(i,j) in DART : j in ITRIANGLE}: tau[j]+0.626*azim[i,j] - 0.77 >= 0;
tau_azim3B{(i,j) in DART : j in ITRIANGLE}: tau[j]-0.259*azim[i,j] + 0.32 >= 0;
tau_azim3C{(i,j) in DART : j in ITRIANGLE}: tau[j]-0.507*azim[i,j] + 0.724 >= 0;
tau_azim3D{(i1,i2,i3,j) in EDART3}: tau[j] + 0.001 -0.18*(y1[i1,i2,i3,j]+y2[i1,i2,i3,j]+y3[i1,i2,i3,j]-6) - 0.125*(y4[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j]-6) >= 0;

tau_azim4A{(i,j) in DART : j in IQUAD}: tau[j] + 4.72*azim[i,j] - 6.248 >= 0;
tau_azim4B{(i,j) in DART : j in IQUAD}: tau[j] + 0.972*azim[i,j] - 1.707 >= 0;
tau_azim4C{(i,j) in DART : j in IQUAD}: tau[j] + 0.7573*azim[i,j] - 1.4333 >= 0;
tau_azim4D{(i,j) in DART : j in IQUAD}: tau[j] + 0.453*azim[i,j] + 0.777 >= 0;

#branch SUPER inequality
tau6h{j in SHEX}: tau[j] >= 0.91;
tau4B{j in SQUAD}: tau[j] >= 0.256;
tau5h{j in SPENT}: tau[j] >= 0.751;
#XX add super8-dih.

#branch FLAT inequality

#branch APIECE inequality

#branch BIGPIECE inequality

#branch BIGTRI inequality
ybig{(i1,i2,i3,j) in EDART3 : j in SMALLTRI}: 
  y4[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j] >= 6.25;

#branch SMALLTRI inequality
ysmall{(i1,i2,i3,j) in EDART3 : j in SMALLTRI}: 
  y4[i1,i2,i3,j]+y5[i1,i2,i3,j]+y6[i1,i2,i3,j] <= 6.25;

#branch HIGHVERTEX inequality
yhigh{i in HIGHVERTEX}: yn[i] >= 2.18;

#branch LOWVERTEX inequality
ylow{i in LOWVERTEX}: yn[i] <= 2.18;

solve;
display graphID;
display lnsum;













