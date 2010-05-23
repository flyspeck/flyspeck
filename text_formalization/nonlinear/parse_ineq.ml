(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Chapter: nonlinear inequalities                                                             *)
(* Author: Roland Zumkeller                                                    *)
(* Date: 2010-05-09                                                    *)
(* ========================================================================== *)

(*
code to parse inequalities.
*)

#load "unix.cma";;

let sergei_path = "sergei/bin/sergei";;

let dest_decimal x = match strip_comb x with
  | (dec,[a;b]) ->                     div_num (dest_numeral a) (dest_numeral b)
  | (sqrt8,[]) when sqrt8 = `sqrt8` -> div_num (Int 3880899) (Int 1372105)
  | _ -> failwith ("dest_decimal: '" ^ string_of_term x ^ "'") ;;

let string_of_num' x = string_of_float (float_of_num x);; (* TODO
correct rounding *)

let rec sergei_of_ccl t =
  let soh = sergei_of_ccl in
  if is_var t then fst (dest_var t) else
  let (f,xs) = strip_comb t in
  let ifix i = let [a;b] = xs in "(" ^ soh a ^ " " ^ i ^ " " ^ soh b ^ ")" in
  let ifix_swapped i = let [b;a] = xs in "(" ^ soh a ^ " " ^ i ^ " " ^
soh b ^ ")" in
  (if not (is_const f) then failwith ("Oracle error: " ^ string_of_term f));
  match fst (dest_const f) with
  | "real_gt" | "real_ge" | "real_sub" -> ifix "-"
  | "real_lt" | "real_le" -> ifix_swapped "-"
  | "real_add" -> ifix "+"
  | "real_mul" -> ifix "*"
  | "real_div" -> ifix "/"
  | "real_pow" -> ifix "^"
  | "\\/" -> ifix "\\/"
  | "atn"      -> let [a] = xs in "Atan [" ^ soh a ^ "]"
  | "sqrt"     -> let [a] = xs in "Sqrt [" ^ soh a ^ "]"
  | "real_neg" -> let [a] = xs in "(-" ^ soh a ^ ")"
  | "pi"       -> let [] = xs in "Pi"
  | "real_of_num" -> let [a] = xs in string_of_num' (dest_numeral a)
(* is this line redundant? *)
  | "NUMERAL" -> let [a] = xs in string_of_num' (dest_numeral t)
  | "DECIMAL" ->  string_of_num' (dest_decimal t)
  | "atn2"      -> let [ab] = xs in let (a,b) = dest_pair ab in  "(" ^
soh a ^ " ATN2 " ^ soh b ^ ")"
  | s -> failwith ("Encountered unknown constant '" ^ s ^ "'");;

let sergei_of_goal (asms,ccl) =
  print_endline "Converting HOL term to sergei format...";
  let vars = map (fun (_,axb) ->
         let (ax,xb) = dest_conj (concl axb) in
         let (a,x) = dest_binary "real_le" ax in
         let (x',b) = dest_binary "real_le" xb in
           if x <> x' then
             failwith ("Malformed assumption: " ^ string_of_term x' ^
                       " should be " ^ string_of_term x ^ ".")
           else
             string_of_num' (dest_decimal a) ^ " <= " ^
             string_of_term x ^ " <= " ^
             string_of_num' (dest_decimal b) ^ " ->\n") asms
  in List.fold_right (^) vars "" ^ " " ^ sergei_of_ccl ccl;;
