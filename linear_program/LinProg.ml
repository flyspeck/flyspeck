#use "hol.ml";;

`[ (#1, 1); (#3, 4) ] , #10`;; (* This represents 1 * x1 + 3 * x4 = 10 *)

`:(real#num) list # real`;; (* Each equation is a list of pairs of real and num and a real *)

(* To give a precise definition of a linear equation, we have to specify that it has no duplicate ":num".
This means each equation contains each variable at most once.

Here I still accept the existence of a weird linear equation: 0 * x0 = 1
*)

let th1 = prove (`?x. x = [#0, 0], #1`, EXISTS_TAC `[#0, 0], #1` THEN MESON_TAC[] );;

new_type_definition "lineq" ("mk_lineq", "dest_lineq") th1;
