let elimin  = REWRITE_RULE[IN];;

(* from hol_til_2005/HOL_TIL_2005/FLYSPECK_PUB_9_2004/hol_light_o/hol-ext/tactics_2.ml:prove_by_refinement *)
let labels_flag = ref false;;
let LABEL_ALL_TAC:tactic = 
 let mk_label avoid =
  let rec mk_one_label i avoid  = 
    let label = "Z-"^(string_of_int i) in
      if not(mem label avoid) then label else mk_one_label (i+1) avoid in
    mk_one_label 0 avoid in
 let update_label i asl = 
  let rec f_at_i f j =
    function [] -> []
      | a::b -> if (j=0) then (f a)::b else a::(f_at_i f (j-1) b) in
  let avoid = map fst asl in
  let current = el i avoid in
  let new_label = mk_label avoid in
  if (String.length current > 0) then asl else 
    f_at_i (fun (_,y) -> (new_label,y) ) i asl in
  fun (asl,w) ->  
    let aslp = ref asl in
    (for i=0 to ((length asl)-1) do (aslp := update_label i !aslp) done;
    (ALL_TAC (!aslp,w)));;

(* new reference *)
let EVERY_STEP_TAC = ref ALL_TAC;;

(*
let e tac = refine(by(VALID 
   (if !labels_flag then (tac THEN (!EVERY_STEP_TAC)) THEN LABEL_ALL_TAC
   else tac)));;
*)

let prove_by_refinement(t,(tacl:tactic list)) = 
  let gstate = mk_goalstate ([],t) in
  let _,sgs,just = rev_itlist 
    (fun tac gs -> by 
       (if !labels_flag then (tac THEN 
         (!EVERY_STEP_TAC) THEN LABEL_ALL_TAC ) else tac) gs)
     tacl gstate in
  let th = if sgs = [] then just null_inst []
  else failwith "BY_REFINEMENT_PROOF: Unsolved goals" in
  let t' = concl th in
  if t' = t then th else
  try EQ_MP (ALPHA t' t) th
  with Failure _ -> failwith "prove_by_refinement: generated wrong theorem";;

