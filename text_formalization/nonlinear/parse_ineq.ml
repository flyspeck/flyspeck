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

(* C form of term *)

let rec ccform t =
  let soh = ccform in
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
  | "\\/" -> ifix "\\/"
  | "real_neg" -> let [a] = xs in "(-" ^ soh a ^ ")"
  | "acs" -> let [a] = xs in "(acos("^soh a^ "))"
(*  
  | "atn"      -> let [a] = xs in "atan (" ^ soh a ^ ")"
  | "sqrt"     -> let [a] = xs in "sqrt(" ^ soh a ^ ")"
  | "sqrt8" -> let [] = xs in "sqrt8"
  | "sqrt2" -> let [] = xs in "sqrt2"
  | "pi"       -> let [] = xs in "pi"
*)
  | "real_of_num" -> let [a] = xs in string_of_num' (dest_numeral a)
(* is this line redundant? *)
  | "NUMERAL" -> let [a] = xs in string_of_num' (dest_numeral t)
  | "DECIMAL" ->  string_of_num' (dest_decimal t)
  | "atn2"      -> let [ab] = xs in let (a,b) = dest_pair ab in  "(" ^
soh a ^ " ATN2 " ^ soh b ^ ")"
  | s -> "(" ^ s ^ "(" ^ join_comma(map soh xs) ^ "))";;


let rec nub = function (* from lpproc *)
  | [] -> []
  | x::xs -> x::filter ((<>) x) (nub xs);;

let cs i =
  let rec cs0 b =function
    | Const (s,_) -> s::b
    | Comb (s,t) -> (cs0 [] s) @ (cs0[] t) @ b
    | Abs(x,t) -> (cs0 b t)
    | _ -> b in
  nub (sort (<) (cs0 [] i ));;

let builtin = [",";"BIT0";"BIT1";"CONS";"DECIMAL"; "NIL"; "NUMERAL"; "_0"; "acs";"dih_y";
    "ineq";  "pi"; "real_add"; "real_div";"real_pow";
    "real_ge"; "real_mul"; "real_of_num"; "real_sub"; "sol_y";
    ];;

let notbuiltin =map (function b -> snd(strip_forall (concl b)))
  [sol0;tau0;hplus;mm1;mm2;(* marchal_quartic; *)Sphere.vol_x;Sphere.sqrt8;Sphere.sqrt2]
  @ [`marchal_quartic h = 
    (sqrt(&2)-h)*(h- hplus )*(&9*(h pow 2) - &17*h + &3)/
      ((sqrt(&2) - &1)* &5 *(hplus - &1))`];;


let args xs = 
  let ls = map (fun s -> "double "^s) xs in
  join_comma ls;;

let ccfunction t = 
  let (lhs,rhs) = dest_eq t in
  let (f,xs) = strip_comb lhs in
  let ss = map ccform xs in
  let p = Printf.sprintf in
  let s = join_lines [
     p"double %s(" (fst (dest_const f));
			args ss;
    p") { \nreturn ( %s ); \n}\n\n"  (ccform rhs);
		       ]
  in s;;
(*
ccfunction `f x y = x +y + #1.0`;;
*)


(* "HJKDESR4" *)

let cc_of_tm iqd = 
  let t = snd(strip_forall iqd) in
  let (vs,i) = dest_comb t in
  let (_,vs) = dest_comb vs in
  let vs = dest_list vs in
  let b = cs t in
  let i = disjuncts i in
  let i = map ccform i in
  let vs = map (fun t -> let (a,b) = dest_pair t in (a,dest_pair b)) vs in
  let vs = map (function (a,(b,c)) -> (ccform a, ccform b, ccform c)) vs in
    (b,vs,i);;

(*
string_of_tm ( (List.nth (getprefix "HJKDESR4") 0).ineq );;
*)

(* generate cfsqp code of ineq *)

let case i j = Printf.sprintf "case %d: *ret = -(%s); break;" j (List.nth i j);;

let vardecl vs = 
  let varname = map (fun (a,b,c) -> b) vs in
  let nvs = List.length vs in
  let  v j = Printf.sprintf "double %s = y[%d];"  (List.nth varname j) j in
    join_lines (map v (0-- (nvs-1)));;

let bounds f vs = 
  let lbs = map f vs in
  join_comma lbs;;

let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);;


let cfsqp_code outs trialcount iqd = 
  let (b,vs,i) = cc_of_tm iqd.ineq in
  let nvs = List.length vs in
  let ni = List.length i in
  let p = Printf.sprintf in
  let s = join_lines ([
    p"// This program is machine generated ";
    p"#include <iomanip.h>\n#include <iostream.h>\n#include <math.h>";
    p"#include \"../Minimizer.h\"\n#include \"../numerical.h\"";
   p"class trialdata { public:   trialdata(Minimizer M,char* s) {     M.coutReport(s);  };};";
  p"int trialcount = %d;\n"  trialcount;
  join_lines(map ccfunction notbuiltin);
   p"void c0(int numargs,int whichFn,double* y, double* ret,void*) {";
  vardecl vs ;
  p"switch(whichFn) {";
  ] @ map (case i) (1-- (-1 + List.length i)) @ [
  p"default: *ret = 0; break; }}\n\n";
  p"void t0(int numargs,int whichFn,double* y, double* ret,void*) {";
  vardecl vs ;
  p"*ret = %s;" (List.nth i 0);
	p"}";
p"Minimizer m0() {";
p"  double xmin[%d]= {" nvs;
(bounds (function (a,b,c) -> a) vs); 
p "};\n  double xmax[%d]= {" nvs;
(bounds (function (a,b,c) -> c) vs); 
p "};\n	Minimizer M(trialcount,%d,%d,xmin,xmax);" nvs (ni-1);
p"	M.func = t0;";
p"	M.cFunc = c0;";
p"	return M;";
p"}";
p "trialdata d0(m0(),\"%s\");\n\n"  iqd.id;
p"int near(double x,double y) {   double eps = 1.0e-8; return (mabs(x-y)<eps); }";
p"int main(){";
    p" assert(near (pi(),4.0*atan(1.0)));";
    p" assert(near (sqrt2(),1.41421356237309));";
    p" assert(near (sqrt8(),2.828427124746190));";
p" assert(near (sol0(),0.5512855984325308));";
p" assert(near (tau0(),1.54065864570856));";
p" assert(near (acos(0.3),1.26610367277949));";
p"assert(near(hplus(),1.3254));";
p"assert(near(mm1(),1.012080868420655));";
p"assert(near(mm2(),0.0254145072695089));";
p"assert(near(real_pow(1.18,2.),1.3924));";
p"assert(near(marchal_quartic(1.18),0.228828103048681825));";
p"}\n\n";
    ]) in
    Printf.fprintf outs "%s" s;;  

(*
  [sol0;tau0;hplus;mm1;mm2;marchal_quartic;Sphere.vol_x;Sphere.sqrt8;Sphere.sqrt2];;
*)

    
let display_cfsqp tmpfile iqd = 
  let outs = open_out tmpfile in
  let _ = cfsqp_code outs 500 iqd in
  let _ = close_out outs in
    Sys.command(sprintf "cat %s" tmpfile);;

let cfsqp_dir = flyspeck_dir^"/../cfsqp";;

display_cfsqp (cfsqp_dir ^ "/tmp/t.cc") test;;

(*
let strip_archive filename = 
  let (ic,oc) = Unix.open_process(sprintf "cat %s | grep -v '//' | grep -v '^$' | sed 's/\"[,;]*//g' | sed 's/_//g' " filename) in
  let s = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
    s;;
*)

