(* Minimizes c.x such that  con[[i, 1]].x ≥ con[[i, 2]] *)


LP[c_, con_] := Module[{i,},
      LinearProgramming[c, Map[First, con], 
      Map[Last, con], Table[-Infinity, {i, Length[c]}]]];

flatTable[x_, {y___}] := Flatten[Table[x, y], Length[{y}] - 1];

(* searching for new inequalities *)

(* Search for a linear lower bound to a nonlinear function on a given domain. \
 
      
      It starts off with the Taylor expansion at the lower corner, then \
checks all the corners of 
      the domain, adjusting the coefficients (by solving a linear program) so \
that proposed lower bound is in fact a lower bound at all of the corners.
  
  *)
(* f nonlinear function.
      lb up lower and upper bounds on the domain. 
      
      Tolerance t. 
      
        implementation assumes a function of at most 9 variables 
  
  
  *)
Clear[SearchLB];
SumRange2[f_, r_] :=
    Apply[Plus, Table[f[r[[i]], i], {i, 1, Length[r]}]];
SumRange[f_, r_] := Apply[Plus, Map[f, r]];
(* standard basis *)
e[i_, j_] := Map[If[# == i, 1, 0] &, Range[j]];

SearchLBp[f_, p_, lb_, up_, t_, extrapoints_] := Module[{f0, delta, len, dif, \
deriv, mkineq, corner, fa, cornerineq, 
      extraineq, d1, d2, d3, d4, d5, d6, d7, d8, d9,
        i1, i2, i3, i4, i5, i6, i7, i8, i9, other, val, ds, y, objective},
      delta = 10^-8;
      len = Length[lb];
      
      (* compute f and derivatives at p *)
      f0 = (f @@ p);
      dif[i_, j_] := If[i == 0, lb[[j]], up[[j]]];
      deriv = Map[(((f @@ (p + delta e[#, len])) - f0)/delta) &, Range[len]];
      
      (* compute corner inequalities *)
      dderiv = deriv - Take[{d1, d2, d3, d4, d5, d6, d7, d8, d9}, len];
      corner[r_] := SumRange2[(dif[#1, #2]e[#2, len]) &, r];
      fa[y__] := f0 + dderiv.Table[{y}[[i]] - p[[i]], {i, 1, len}];
      mkineq[{y___}] := fa[y] - f[y] ≤ t;
      cornerineq = flatTable[
        mkineq[corner @ 
          Take[{i1, 
            i2, i3, i4, i5, i6, i7, i8, i9}, len]], Take[{{i1, 0, 1}, {i2, 0, 
              1}, {i3, 0, 1}, {i4, 0, 1}, {i5, 
      0, 1}, {i6, 0, 1}, {i7, 0, 1}, {i8, 0, 1}, {i9, 0, 1}}, len]] ;
      
      (* extra inequalities *)
      extraineq = Map[mkineq, extrapoints];
      
      pos = {}; (* {d1 ≥ 0, d2 ≥ 0, d3 ≥ 0, d4 ≥ 0, d5 ≥ 0, d6 ≥ 0}; *)
      (* adjust "other" with 
      special constraints, such as desired symmetries *)
      other = {}; (*  {  d2 == d3, d5 == d6}; *)
      
      (* minimize *)
      objective = Apply[Plus, Take[{Abs[d1], Abs[d2], 
          Abs[d3], Abs[
            d4], Abs[d5], Abs[d6], Abs[d7], Abs[d8], Abs[d9]}, len]];
      {val, ds} = NMinimize[Join[{objective}, cornerineq, extraineq, 
              pos, other], Take[{d1, d2, d3, d4, d5, d6, d7, d8, d9}, len]];
      {"corner", f0 - t, "derivs", deriv, "approx", dderiv} /. ds
      ];

SearchLB[f_, lb_, up_, t_, extrapoints_] := SearchLBp[f, lb,
             lb, up, t, extrapoints];



(* Functions for interpolation.  Taken from *)

UpperHullPred[p_, x_List] := Module[{s1, tab, pos}, s1 = 
    Select[x, (#[[1]] < p[[1]] - 0.001) &];
      If[s1 == {}, Return[{}]];
      tab = Table[Slope[p, s1[[i]]], {i, 1, Length[s1]}];
      pos = Min[Position[tab, Min[tab]]];
      s1[[pos]]];

UpperHullSucc[p_, 
      x_List] := 
        Module[{s1, tab, pos}, s1 = Select[x, (#[[1]] > p[[1]] + 0.001) &];
      If[s1 == {}, Return[{}]];
      tab = Table[Slope[p, s1[[i]]], {i, 1, Length[s1]}];
      pos = Max[Position[tab, Max[tab]]];
      s1[[pos]]];

UpperInterpolate[x_, v_List] := Module[{up, u1, pos, c1, 
    c2, down, d1}, up = Select[v, (#[[1]] ≥ N[x]) &];
      If[up == {}, Return[-Infinity]];
      u1 = Table[up[[i, 1]], {i, 1, Length[up]}];
      pos = Position[u1, Min[u1]] // Min;
      c2 = up[[pos]];
      down = Select[v, (#[[1]] < N[x]) &];
      If[down == {}, Return[-Infinity]];
      d1 = Table[down[[i, 1]], {i, 1, Length[down]}];
      pos = Position[d1, Max[d1]] // Max;
      c1 = down[[pos]];
      Interpolate[N[x], c1, c2][[2]]];

FormUpperHull[x_List] := 
    Module[{t2, pos, currenttop, firsttop, temp}, t2 = Table[
        x[[i, 2]], {i, 1, Length[x]}];
      pos = Position[t2, Max[t2]] // Max;
      currenttop = x[[pos]];
      firsttop = x[[pos]];
      temp = {currenttop};
      While[currenttop ≠ {}, currenttop = UpperHullSucc[currenttop, x];
        AppendTo[temp, currenttop];];
      currenttop = firsttop;
      While[currenttop ≠ {}, currenttop = UpperHullPred[currenttop, x];
        AppendTo[temp, currenttop];];
      Complement[temp, {{}}]];
FormLowerHull[x_List] := Module[{revx, v},
      revx[v_List] := Map[{#[[1]], -#[[2]]} &, v];
      revx[FormUpperHull[revx[x]]]];

InterpolateAlongHull[t_, x_List] := Module[{low, hi, i, s, sp, sel},
      sel = Select[x, (First[#] < t) &];
      low = If[Length[sel] > 0, sel // Last, x // First];
      i = Position[x, low] // Flatten // First;
      hi = If[i < Length[x], x[[i + 1]], x[[i - 1]]];
      sp = (s /. Solve[t == s (low[[
      1]]) + (1 - s) (hi[[1]]), s]) // Flatten // First;
      sp (low[[2]]) + (1 - sp)(hi[[2]])
      ];
(* InterpolateAlongHull[1, {{2, 4}, {4, 7}, {5, 22}}] *)

