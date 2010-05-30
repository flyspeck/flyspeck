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

(* #load "unix.cma";; *)

(* let sergei_path = "sergei/bin/sergei";; *)

let dest_decimal x = match strip_comb x with
  | (dec,[a;b]) ->                     div_num (dest_numeral a) (dest_numeral b)
(*  | (sqrt8,[]) when sqrt8 = `sqrt8` -> div_num (Int 3880899) (Int 1372105)  *)
  | _ -> failwith ("dest_decimal: '" ^ string_of_term x ^ "'") ;;

let string_of_num' x = string_of_float (float_of_num x);; (* TODO
correct rounding *)

let unsplit d f = function
  | (x::xs) ->  List.fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

let join_comma  = unsplit "," (fun x-> x);;

let rec cc_of_ineq t =
  let soh = cc_of_ineq in
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
(*  
  | "atn"      -> let [a] = xs in "atan (" ^ soh a ^ ")"
  | "sqrt"     -> let [a] = xs in "sqrt(" ^ soh a ^ ")"
*)
  | "real_neg" -> let [a] = xs in "(-" ^ soh a ^ ")"
  | "sqrt8" -> let [] = xs in "sqrt8"
  | "sqrt2" -> let [] = xs in "sqrt2"
  | "pi"       -> let [] = xs in "pi"
  | "real_of_num" -> let [a] = xs in string_of_num' (dest_numeral a)
(* is this line redundant? *)
  | "NUMERAL" -> let [a] = xs in string_of_num' (dest_numeral t)
  | "DECIMAL" ->  string_of_num' (dest_decimal t)
  | "atn2"      -> let [ab] = xs in let (a,b) = dest_pair ab in  "(" ^
soh a ^ " ATN2 " ^ soh b ^ ")"
  | s -> "(" ^ s ^ "(" ^ join_comma(map soh xs) ^ "))";;


(* "HJKDESR4" *)

let string_of_ineq iqd = 
  let t = snd(strip_forall iqd) in
  let (vs,i) = dest_comb t in
  let (_,vs) = dest_comb vs in
  let vs = dest_list vs in
  let i = disjuncts i in
  let i = map cc_of_ineq i in
  let vs = map (fun t -> let (a,b) = dest_pair t in (a,dest_pair b)) vs in
  let vs = map (function (a,(b,c)) -> (cc_of_ineq a, cc_of_ineq b, cc_of_ineq c)) vs in
    (vs,i);;

(*
string_of_ineq ( (List.nth (getprefix "HJKDESR4") 0).ineq );;
*)

(* generate cfsqp code of ineq *)


  let p = Printf.sprintf in
  let j = join_lines [
    p"#include <iomanip.h>\n#include <iostream.h>\n#include <math.h>";
    p"#include \"Minimizer.h\n#include \"numerical.h";
   p"class trialdata { public:   trialdata(Minimizer M,char* s) {     M.coutReport(s);  };};";
  p"int trialcount = 300;\n" ;
   p"void constraint(int numargs,int whichFn,double* y, double* ret,void*) {";
  p"switch(whichFn) {";
  (* cases *)
  p"case 1: *ret = %s;  break;";
  p"case 2: *ret = %s;  break;";
  p"default: *ret = 0; break; }}\n\n";
  p"void t0(int numargs,int whichFn,double* y, double* ret,void*) {";
  p"*ret = %s";
	p"}";
p"Minimizer m0() {";
p"  double xmin[%d]= {2,2,2,2,2,2};";
p"  double xmax[%d]= {sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0),sqrt(8.0)};";
p"	Minimizer M(trialcount,%d,%d,xmin,xmax);"
p"	M.func = t0;";
p"	M.cFunc = c0;";
p"	return M;";
p"}";
p"trialdata d0(m0(),\"%s\");\n\n" XX;
p"int main(){}"
   ] in
    Printf.fprintf outs "%s" j;;  

    
