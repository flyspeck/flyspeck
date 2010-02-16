
(* given vertex v, with length 2, 
   and vertex w with length t0, form a triangle 
   0,v,w where |v-w| = lambda 
   
   We show by simplet trigonometry that 
   mu(C(2, 3.07-t0, Pi)) >> 0.178

   for squander we need the volume and the solid angle.

   For the solid angle, we
   determine the angle beta between (0,v) and (0,w)
   and use the formula 2 Pi (1-Cos[beta]) for the solid
   angle of a cone.

   For the volume, we compute the volume spanned by the cone
   and take 
*) 

t0 = 1.25841
lambda = 3.07 - t0
M = 0.42755

(* lower angle 
use the law of cosines
*) 
beta = ArcCos[(lambda^2 - 2^2 - t0^2)/(- 2 2 t0)]//N

(* solid angle 
divide by 2 because the angle is Pi, not 2 Pi
*) 
sol = (2 Pi (1 - Cos[beta])) / 2

(* volume *) 
vol = ((4/3 Pi t0^3) * (sol / (4 Pi))) 

(* squander *) 
res = vol - M sol
