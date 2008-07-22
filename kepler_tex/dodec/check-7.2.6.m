
(* given vertex v, with length 2, 
   and vertex w with length t0, form a triangle 
   0,v,w where |v-w| = lambda 
   
   We show by simplet trigonometry that 
   mu(C(2, 3.07-t0, Pi)) >> 0.178

   for squander we need the volume and the solid angle.
   For the volume, we compute two pieces using the formula
   for the volume of a cone.  For the solid angle, we
   determine the angle beta between (0,v) and (0,w)
   and use the formula 2 Pi (1-Cos[beta]) for the solid
   angle of a cone.
*) 

t0 = 1.25841
lambda = 3.07 - t0
M = 0.42755

(* upper angle *) 
alpha = ArcCos[(t0^2 - 2^2 - lambda^2)/(- 2 2 lambda)]//N

(* lower angle *) 
beta = ArcCos[(lambda^2 - 2^2 - t0^2)/(- 2 2 t0)]//N

(* side angle *) 
gamma = Pi - alpha - beta

(* top side angle *)
gamma1 = Pi/2 - alpha

(* top part of v *)
h1 = lambda Sin[gamma1] / (Pi / 2) //N

(* distance from w to line (0,v) *)
r = Sqrt[lambda^2 - h1^2]

(* top volume *)
v1 = 1/2 (1/3 Pi r^2 h1)

(* bottom part of v*) 
h2 = 2 - h1

(* bottom volume *)
v2 = 1/2 (1/3 Pi r^2 h2)

(* volume *) 
vol = v1 + v2

(* solid angle *) 
sol = 2 Pi (1 - Cos[beta])

(* squander *) 
res = vol - M sol
