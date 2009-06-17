(*
Linear Programming Inequalities for 2009 proof.


******************
variables:

azim[dart]
ln[dart]     // =L[yn[dart]/2]
lnazim[dart]  // =ln[dart]*azim[dart]
yn[dart]
ye[dart]
sol[dart]
tau[dart]

******************

optional variables for later versions:
diag[dart,dart]  // diagonals.
azimdiag

*******************
equality relations:
yn[dart] depends only on the node
ln[dart] depends only on the node
ye[dart] depends only on the edge
sol[dart] depends only on the face
tau[dart] depends only on the face
SUM of azim around each node is 2Pi.
SUM of lnazim around each node is 2Pi*ln
SUM of azim around each face is sol + (n-2)*Pi, where n = CARD(face).
SUM of lnazim around each face is "tau def XX -flypaper.pdf:100"
ln[dart] = linear interpolation in yn[dart] of {2,1}, {2.52,0}.
  =   2*(2.52 - yn)/0.52

*********************
variable bounds:

0 <= azim <= Pi
0 <= ln <= 1.
0 <= lnazim <= Pi
2 <= yn <= 2.52
2 <= ye <= 2.52
0 <= sol <= 4*Pi
0 <= tau <= tgt (squander target)

******************

inequalities (new J-series):

******************
azim inequalities:
******************
lnazim inequalities:
******************
sol inequalities:
******************
tau inequalities:



*)
