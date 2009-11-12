#use "hol.ml";;

(*Define the type of linea equation*)
let has_nonzero_DEF = define `has_nonzero vs = (?x. (MEM x vs) /\ ~(x = #0))`;;
let lineq_THM = prove(`?(eq: real list # real). has_nonzero (FST eq)`,
 EXISTS_TAC `[#1], #0` THEN
 REWRITE_TAC [FST_DEF; has_nonzero_DEF; MEM] THEN
 EXISTS_TAC `#1` THEN
 ARITH_TAC);;

let lineq_BIJ = new_type_definition "lineq" ("mk_lineq", "dest_lineq") lineq_THM;

(*Define the notion of solution*)
let is_solution_DEF = define `is_solution (x:real list) (eq:lineq) = F`;;

(*Prove the most basic theorem of multiplying both side with the same non-zero integer*)
