(* 

Format: Mathematica file
Author: Thomas C. Hales
Date: September 2012
Article: http://arxiv.org/abs/1209.6043
Title: A proof of Fejes Toth's conjecture on sphere packings with kissing number twelve.

The file sphere.m should be loaded first.
mathematica/sphere.m at https://github.com/flyspeck/flyspeck

ID of this file: "HFBBNUL".  
*)


(* Definition of the function d3 from the paper *)

sq8 := Sqrt[8.0];
dA := 0.103;
dB := 0.27; 
d3[r_, s_, t_] := If[r + s + t != 3, "Error",
   If[r == 3, 0,
    If[r == 2, dA - dA*t,
     dA *(2 - (s + t)) + dB *(r + 2 (s + t) - 4) + dA * t]]];

boundmax[a_, b_] := (x /. Solve[eta[a, b, x] == Sqrt[3], x]);

bmNumeric = {boundmax[2, 2], boundmax[2, 2.52], boundmax[2.52, 2.52], 
    boundmax[2.52, 3.0], boundmax[3.0, 3.0]} // Max;

(* some edge bounds *)
bm0 = 3.45;  (* for (r,s,t)=(1,1,1) *)
bm1 = Sqrt[32/3];  (* 3.45819..., for (2,0,1) *)
bm2 = 3.459; (* generic upper bound *)
bm3 = 2 Sqrt[3.0] // N ; (* 3.4641..., for (1,1,1) *)

test1 = (bm2 > bmNumeric) && (2^2 + 2.6^2 < 3.45^2) (* obtuseness test *) &&
  (eta[2, 2.6, bm0]^2 > 3) (* two cases : bm <=  bm0 or mid edge >= 2.6 *) 

  

  (* solid angle of a simplex from sphere.m *)
sol[y4_, y5_, y6_] := Solid[2, 2, 2, y4, y5, y6];  


(* count the number of edges in different ranges *)
count[{i_, j_, k_}] :=
  Module[{f, p, ch},
   f = {{1, 0, 0}, {0, 1, 0}, {0, 0, 1}};
   ch[p_] := f[[p]];
   ch[i] + ch[j] + ch[k]];

(* this is the main loop for checking constants d3 *)
  
docase[i_, j_, k_] := Module[{r, s, t, h1, h2, h3, p1, p2, p3, m, n,cases},
  cases = {{2, 2}, {2.52, 3.0}, {3.0, bm2}};
  {r, s, t} = count[{i, j, k}];
  h1 = cases[[i]];
  h2 = cases[[j]];
  h3 = cases[[k]];
  If[{r, s, t} == {2, 0, 1}, h3[[2]] = bm1];
  m = Table[
     sol[h1[[p1]], h2[[p2]], h3[[p3]]], {p1, 1, 2}, {p2, 1, 2}, {p3, 
      1, 2}] // N;
  n = Min[m] - sol0 - d3[r, s, t];
  If[{r, s, t} == {1, 1, 1} (* exclude for now *), 0,
   If[i > j || j > k, 0 (* symmetries *),
    n]]]

test2 = (Min[
     Table[{docase[v1, v2, v3]}, {v1, 1, 3}, {v2, 1, 3}, {v3, 1, 
       3}]] == 0);


(* this is the secondary loop for checking constants d3[1,1,1] *)
  
doaltcase[r_] := 
 Module[{h1, h2, h3,altcases},
  altcases = {{{2, 2}, {2.52, 2.6}, {3.0, bm0}}, {{2, 2}, {2.6, 
     3.0}, {3.0, bm3}}};
  {h1, h2, h3} = altcases[[r]];
  m = Table[
     sol[h1[[p1]], h2[[p2]], h3[[p3]]], {p1, 1, 2}, {p2, 1, 2}, {p3, 
      1, 2}] // N;
  n = Min[m] - sol0 - d3[1, 1, 1];
  n]

alltest = test1 && test2 && doaltcase[1] > 0 && doaltcase[2] > 0

(* end of testing constants d3 *)



(* 6621965370 *)
(* The article claims that \
Dihedral[2,2,2,2,y5,y6]<2Pi/5, when y5,y6>= 2.52 .  We can do a \
derivative calculation to reduce to
Dihedral[2,2,2,2,2.52,2.52]<2Pi/5 *) 
uu = Sqrt[Delta[2, 2, 2, 2, x, y]] D[
     DihedralAlt[2, 2, 2, 2, x, y] // Rationalize, x] // 
   Simplify;  (* evident signs *)
Solve[(uu /. {y -> 2.52}) == 0, x];

(*
This is the case mU = 5 in Fejes Toth's \
Full Contact conjecture.
We might have the situation of a pentagon perimeter, one enclosed, \
and one edge connection.
In this case, two of the triangles have parameters \
Dihedral[2,2,2,2,y5,y6], where y5 in [2,2.52] and y6 >= 2.52.
We can still get the desired bound in this case.
*)