(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Mathematica code for Dense Sphere Packings: A formal blueprint *)
(* Library of Basic Functions *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2010-05-22                                                           *)
(* ========================================================================== *)

BeginPackage["Sphere`"] 

guid::usage = "guid generates a random uppercase  alphabetical  string";

randomint::usage = "randomint generates a random 9 digit integer";

flatTable::usage = "flatTable[f, {range1,range2,...}] gives a flattened table of
  the function f over the given multivariate ranges";

arc::usage = "arc[x,y,z] is the angle opposite z in a triangle with edges x y z.";

$SpherePrecision::usage= "specifies the working precision in the Sphere` package";

Ns::usage = "Ns[x] approximates x to precision $SpherePrecision";

doct::usage = "doct = 0.72... is the density of an octahedron";

chi::usage = "chi a polynomial (in x) in six variables";

Chi::usage = "Chi[y1,..,y6] evaluates the polynomial chi ";

eta::usage = "eta[x, y, z] circumradius of a triangle with sides x,y,z";

volR::usage = "volR[a, b, c] volume of a Rogers simplex";

solR::usage = "solR[a,b,c] solid angle of a Rogers simplex ";

solRAlt::usage = "solRAlt[a, b, c] = alternative solid angle formula for the Rogers simplex";

dihR::usage = "dihR[a,b,c]  dihedral angle of a Rogers simplex";

Solid::usage = "Solid[y1, y2, y3, y4, y5, y6] = solid angle of a simplex ";

SolidAlt::usage = "SolidAlt[y1_, y2_, y3_, y4_, y5_, y6_] = solid angle";

Dihedral::usage = "Dihedral[y1, y2, y3, y4, y5, y6] ";

DihedralAlt::usage = "DihedralAlt[y1, y2, y3, y4, y5, y6] ";
                    
                    
Dihedral2::usage = "Dihedral2[y1, y2, y3, y4, y5, y6] dihedral angle along the second edge";

Dihedral3::usage = "Dihedral3[y1, y2, y3, y4, y5, y6] ";

DeltaX::usage = "DeltaX[x1, x2, x3, x4, x5, x6] = Delta function";

Delta::usage = "Delta[y1, y2, y3, y4, y5, y6] Delta function in terms of unsquared y";

Ups::usage = "Ups[x1, x2, x6] = upsilon function";

Rho::usage = "Rho[y1, y2, y3, y4, y5, y6] = polynomial";

Rad::usage = "Rad[y1, y2, y3, y4, y5, y6] = circumradius of a simplex";


cosarc::usage = "cosarc[a, b, c]=Cos[arc[a,b,c]] ";

norm::usage = "norm[x] length of vector x";

norm::usage = "norm[x, y] distance squared";

Distance::usage = "Distance[x, y] Euclidean distance";

FarFrom::usage = "FarFrom[x, pair] = the element of pair farther from point x";

ExtremePoint::usage = "ExtremePoint[{x, y, z}] ";

Vertex::usage = "Vertex[{X, dx}, {Y, dy}, {Z, dz}] is a point at distances dx,dy,dz from points X,Y,Z";

SimplexCoordinates::usage = "SimplexCoordinates[y1, y2, y3, y4, y5, y6] ";

Enclosed::usage = "Enclosed[x, z1, z2, z3] ";

CrossDiag::usage = "CrossDiag[y1, y2, y3, y4, y5, y6, y7, y8, y9] ";

NullVector::usage = "NullVector={0,0,0} ";



bisect::usage = "bisect[{f, x, y, eps}] ";

bisection::usage = "bisection[f, x, y, eps] ";

interp::usage = "interp[x,p,q] = f[x] where f is the line through p and q";

Slope::usage = "Slope[p, q] is the slope of the line through p and q ";



Begin["`Private`"] 

SeedRandom[];

guid := Module[{ra},
               ra := FromCharacterCode[64 + Random[Integer, {1, 26}]];
               StringJoin[Table[ra, {i, 1, 7}]]
               ];

randomint :=Random[Integer, {10^9, 10^10}];

Off[General::spell1];
Install = {};

(Unprotect[In, Out]; Format[In] = SphereIn;
  Format[Out] = SphereOut; Protect[In, Out];)

flatTable[x_, {y___}] := Flatten[Table[x, y], Length[{y}] - 1];

$SpherePrecision := 16;
Ns[x_] := N[x, $SpherePrecision];
doct := ((Pi - 4*ArcTan[2^(1/2)/5])/(2*2^(1/2))) // Ns;

chi = -(x1*
    x4^2) + x1*x4*x5 + x2*x4*x5 - x2*x5^2 + x1*x4*x6 + x3*x4*x6 + x2*x5*
      x6 + x3*x5*x6 - 2*x4*x5*x6 - x3*x6^2;

eta[x_, y_, z_] := Module[{s = (x + y + z)/2}, x y z/4/Sqrt[s (s - x)(
      s - y)(s - z)]] // Ns;

volR[a_, b_, c_] := Sqrt[a^2*(b^2 - a^2)*(c^2 - b^2)]/6 // Ns;

solR[x_, y_, z_] := 2*ArcTan[Sqrt[((z - y)*(y - x))/((
        z + y)*(x + y))]] // Ns;

dihR[x_, y_, z_] := ArcTan[Sqrt[(z^2 - y^2)/(y^2 - x^2)]] // Ns;

ChiX[x__] := Module[{x1, x2, x3, x4, x5, x6}, {x1, x2, x3, 
      x4, x5, x6} = {x};
      -(x1*x4^2) + x1*x4*x5 + x2*x4*x5 - x2*x5^2 + x1*x4*x6 + x3*x4*x6 + 
      x2*x5*x6 + x3*x5*x6 - 2*x4*x5*x6 - x3*x6^2];

Chi[y__] := ChiX @@ ({y}^2);

DeltaX[x1_, x2_, x3_, x4_, x5_, x6_] :=
    (x1*x4*(-x1 + x2 + x3 - x4 + x5 + x6) + x2*
    x5*(x1 - x2 + 
          x3 + x4 - x5 + x6) + x3*x6*(x1 + x2 - x3 + x4 + x5 - x6) - x2*x3*
        x4 - x1*x3*x5 - x1*x2*x6 - x4*x5*x6);

Delta[y1_, y2_, y3_, y4_, y5_, y6_] := (DeltaX @@ ({y1, y2, y3, y4, y5, 
              y6}^2)); 

Ups[x1_, x2_, x6_] := -x1*x1 - x2*x2 - x6*x6 + 2*x1*x6 + 2*x1*x2 + 2*x2*x6;


Rho[y1_, y2_, y3_, y4_, y5_, y6_] := Module[{x1, x2, x3, x4, x5, x6}, x1 = 
      y1*y1; x2 = y2*y2; x3 = y3*y3;
      x4 = y4*y4; x5 = y5*y5; x6 = y6*y6;
      (-x1*x1*x4*x4 - x2*x2*x5*x5 - x3*x3*x6*x6 + 2*x1*x2*x4*x5 + 2*x1*x3*x4*
      x6 + 2*x2*x3*x5*x6)];

Rad[y1_, y2_, y3_, y4_, y5_, y6_] := Sqrt[Rho[y1, y2, y3, y4, y5, y6]/Delta[
      y1, y2, y3, y4, y5, y6]]/2;

Dihedral[y1_, y2_, y3_, y4_, y5_, y6_] := Module[{ux, x1, x2, x3, x4, x5, x6, 
        t}, x1 = y1*y1; x2 = y2*y2; x3 = y3*y3;
      x4 = y4*y4; x5 = y5*y5; x6 = y6*y6;
      ux = Ups[x1, x2, x6]*Ups[x1, x3, x5];
      t = (-2*x1*x4 + x1*(x2 + x3 + x5 + x6) + x2*x5 + x3*x6 - x1*x1 - x2*x3 -
       x5*x6)/Sqrt[ux];
      ArcCos[t]];

(*In terms of arctan*)
DihedralAlt[y1_, y2_, y3_, y4_, y5_, y6_] := Module[{t, del, d4, x1 = y1*y1, 
      x2 = y2*y2, x3 = y3*y3, x4 = y4*y4, 
    x5 = y5*y5, x6 = y6*y6}, del = Delta @@ Sqrt[{x1, x2, x3, t, x5, x6}];
      d4 = D[del, t];
      Pi/2 - ArcTan[d4/Sqrt[4 x1 del]] /. {t -> x4}];

Dihedral2[y1_, y2_, y3_, y4_, y5_, y6_] :=(*Dihedral along edge 2*)
      Dihedral[y2, y1, y3, y5, y4, y6];


Dihedral3[y1_, y2_, y3_, y4_, y5_, y6_] :=(*Dihedral along edge 
      3*)Dihedral[y3, y1, y2, y6, y4, y5];


aSolid[y1_, y2_, y3_, y4_, y5_, y6_] := y1*y2*y3 + y1*(y2*y2 + y3*y3 - y4*y4)/
    2 + y2*(y1*y1 + y3*y3 - y5*y5)/2 + y3*(y1*y1 + y2*y2 - y6*y6)/2;

SolidAlt[y1_, y2_, y3_, y4_, y5_, y6_] := Module[{u, t, a1}, u = Delta[y1, y2, 
    y3, y4, y5, y6];
        If[N[u] ≤ 0, Return[0]];
        t = Sqrt[u]/2;
        a1 = aSolid[y1, y2, y3, y4, y5, y6];
        2*ArcTan[t/a1]] // Ns;

Solid[y1_, y2_, y3_, y4_, y5_, y6_]:=
  (Dihedral[y1,y2,y3,y4,y5,y6]+Dihedral2[y1,y2,y3,y4,y5,y6]+
   Dihedral3[y1,y2,y3,y4,y5,y6]-Pi);

solRAlt[a_, b_, c_] := Module[{y1 = a, y2 = b,
     y3 = c, y4, 
      y5, y6}, y4 = Sqrt[c^2 - b^2]; y5 = Sqrt[c^2 - a^2]; y6 = 
        Sqrt[b^2 - a^2];
      DihedralAlt[y1, y2, y3, y4, y5, y6] + 
      Dihedral2Alt[y1, y2, y3, y4, y5, y6] + Dihedral3Alt[y1, 
        y2, y3, y4, y5, y6] - Pi];






arc[a_, b_, c_] := ArcCos[(a^2 + b^2 - c^2)/(2 a b)];
cosarc[a_, b_, c_] := (a^2 + b^2 - c^2)/(2 a b);

norm[x_] := x.x;
norm[x_, y_] := norm[x - y];
Distance[x_, y_] := Sqrt[(x - y).(x - y)];

FarFrom[x_, pair_] := 
      If[norm[x, pair[[1]]] < norm[x, pair[[2]]], pair[[2]], pair[[1]]];

ExtremePoint[{x_, y_, z_}] := LinearSolve[{x, y, z}, {x.x/2, y.y/2, z.z/2}];

Vertex[{X_, 
dx_}, {Y_, dy_}, {Z_, dz_}] := Simplify[Module[{w, x, y, z}, w = {x, y, z};
        w /. Solve[{norm[X, 
      w] == dx^2, norm[Y, w] == dy^2, norm[Z, w] == dz^2}, w]]];

SimplexCoordinates[y1_, y2_, y3_, y4_, y5_, y6_] := Module[{x1, x2, x3, x4, 
    x5, x6, X, Y, Z}, x1 = y1^2; x2 = y2^2; x3 = y3^2;
      x4 = y4^2; x5 = y5^2; x6 = y6^2;
      X = {x1^(1/2), 0, 0};
      Y = {(x1 + x2 - x6)/(2*x1^(1/2)), (-x1^2 + 2*x1*x2 - x2^2 + 2*x1*
      x6 + 2*x2*x6 - x6^2)^(1/2)/(2*x1^(1/2)), 0}; Z = {(x1 + x3 - x5)/(2*x1^(
      1/2)), -((x1^2 - x1*x2 - x1*x3 + x2*x3 + 2*x1*x4 - x1*x5 - x2*
      x5 - x1*x6 - x3*x6 + x5*x6)/(2*x1^(1/2)*(-x1^2 + 2*x1*x2 - x2^2 + 2*
          x1*x6 + 2*x2*x6 - x6^2)^(1/2))), (-(x2*x3*x4) - x1*
                  x3*x5 - x1*x2*x6 - x4*x5*x6 + x3*(x1 + x2 - x3 + x4 + 
              x5 - x6)*x6 + x2*x5*(x1 - x2 + x3 + x4 - x5 + 
      x6) + x1*x4*(-x1 + x2 + x3 - x4 + x5 + x6))^(1/2)/(-x1^2 + 2*x1*x2 - 
          x2^2 + 2*x1*x6 + 2*x2*x6 - x6^2)^(1/2)}; {X, Y, Z}] // Ns

Enclosed[x__, z1_, z2_, z3_] := Module[{X, Y, Z}, If[Length[{x}]
     != 6, Return["invalid input"]];
      {X, Y, Z} = SimplexCoordinates[x];
      Sqrt[norm[FarFrom[NullVector, Vertex[{X, z1}, {Y, z2}, {Z, z3}]]]]];

CrossDiag[y1_, y2_, y3_, y4_, y5_, y6_, y7_, y8_, y9_] := Enclosed[y1, y5, y6,
       y4, y2, y3, y7, y8, y9];

NullVector = {0, 0, 0};


bisect[{f_, x_, y_, eps_}] := Module[{u = (x + y)/2., fx = f[x], fu}, fu = N[f[u]];
      Which[Abs[fu] < eps, {f, x, y, eps}, 
           fx*fu <  0, bisect[{f, x, u, eps}], 
           fu*f[y] < 0, bisect[{f, u, y, eps}]]];

bisection[f_, x_, y_, eps_] := Which[x > y, "FAIL (inverted interval)", 
        N[f[x] f[y]] > 0, "FAIL (f has fixed sign)", 
        True, bisect[{f, x, y, eps}]];

interp[x_, {x1_, y1_}, {x2_, y2_}] := y1 + (x - x1) (y2 - y1)/(x2 - x1);

Slope[p_, q_] := (p[[2]] - q[[2]])/(p[[1]] - q[[1]]);


End[] 
EndPackage[]; 