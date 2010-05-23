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
(* Interp