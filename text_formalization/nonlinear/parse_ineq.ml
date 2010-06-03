(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Chapter: nonlinear inequalities                                                             *)
(* Author: Roland Zumkeller and Thomas Hales           *)
(* Date: 2010-05-09                                                    *)
(* ========================================================================== *)

(*
code to parse inequalities and generate a cfsqp file to test nonlinear inequality.
*)

let dest_decimal x = match strip_comb x with
  | (dec,[a;b]) ->                     div_num (dest_numeral a) (dest_numeral b)
  | _ -> failwith ("dest_decimal: '" ^ string_of_term x ^ "'") ;;

let string_of_num' x = string_of_float (float_of_num x);; (* TODO
correct rounding *)

let unsplit d f = function
  | (x::xs) ->  List.fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

let join_comma  = unsplit "," (fun x-> x);;

let join_lines  = unsplit "\n" (fun x-> x);;

let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);; (* from HOL Light lib.ml *)

let rec nub = function (* from lpproc *)
  | [] -> []
  | x::xs -> x::filter ((<>) x) (nub xs);;

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
  | "real_of_num" -> let [a] = xs in string_of_num' (dest_numeral a)
(* is this line redundant? *)
  | "NUMERAL" -> let [a] = xs in string_of_num' (dest_numeral t)
  | "DECIMAL" ->  string_of_num' (dest_decimal t)
  | "atn2"      -> let [ab] = xs in let (a,b) = dest_pair ab in  "(" ^
soh a ^ " ATN2 " ^ soh b ^ ")"
  | s -> "(" ^ s ^ "(" ^ join_comma(map soh xs) ^ "))";;

let ccform1 t = 
   try (ccform t) with Failure s -> failwith (s^" .......   "^string_of_term t);;




let cs i =
  let rec cs0 b =function
    | Const (s,_) -> s::b
    | Comb (s,t) -> (cs0 [] s) @ (cs0[] t) @ b
    | Abs(x,t) -> (cs0 b t)
    | _ -> b in
  nub (sort (<) (cs0 [] i ));;

let builtin = [",";"BIT0";"BIT1";"CONS";"DECIMAL"; "NIL"; "NUMERAL"; "_0"; "acs";"dih_y";
    "ineq";  "pi"; "real_add"; "real_div";"real_pow";
    "real_ge"; "real_mul"; "real_of_num"; "real_sub"; "sol_y";"hminus";"lmfun";"wtcount3_y";
    "wtcount6_y";"beta_bump_y";"machine_eps"
    ];;

let strip_let t = REWRITE_RULE[REDEPTH_CONV let_CONV (concl t )] t;;

let notbuiltin = ref[];;

notbuiltin :=map (function b -> snd(strip_forall (concl (strip_let b))))
  [sol0;tau0;hplus;mm1;mm2;Sphere.vol_x;Sphere.sqrt8;Sphere.sqrt2;Sphere.rho_x;
   Sphere.rad2_x;Sphere.ups_x;Sphere.eta_x;Sphere.eta_y;vol_y;vol3r;norm2hh;
 beta_bump_force_y;  a_spine5;b_spine5;beta_bump_lb]
(*   @ [marchal_quartic;vol2r];; *)
  @ [`marchal_quartic h = 
    (sqrt(&2)-h)*(h- hplus )*(&9*(h pow 2) - &17*h + &3)/
      ((sqrt(&2) - &1)* &5 *(hplus - &1))`;`vol2r y r = &2 * pi * (r*r - (y / (&2)) pow 2)/(&3)`];;
!notbuiltin;;
(* remove these entirely before converting to C *)

let elim_list = ref [];;
elim_list := [gamma4f;vol4f;y_of_x;vol_y;vol3f;vol2f;gamma3f;gamma23f;REAL_MUL_LZERO;
   REAL_MUL_RZERO];;
!elim_list;;

let prep_term t = 
  let t' = REWRITE_CONV (!elim_list) t in
  let (a,b)=  dest_eq (concl t') in
    b;;


let args xs = 
  let ls = map (fun s -> "double "^s) xs in
  join_comma ls;;

let ccfunction t = 
  let (lhs,rhs) = dest_eq t in
  let (f,xs) = strip_comb lhs in
  let ss = map ccform1 xs in
  let p = Printf.sprintf in
  let s = join_lines [
     p"double %s(" (fst (dest_const f));
			args ss;
    p") { \nreturn ( %s ); \n}\n\n"  (ccform1 rhs);
		       ]
  in s;;
(*
ccfunction `f x y = x +y + #1.0`;;
*)


let cc_of_tm tm = 
  let t = snd(strip_forall (prep_term (tm))) in
  let (vs,i) = dest_comb t in
  let (_,vs) = dest_comb vs in
  let vs = dest_list vs in
  let b = cs t in
  let i = disjuncts i in
  let i = map ccform1 i in
  let vs = map (fun t -> let (a,b) = dest_pair t in (a,dest_pair b)) vs in
  let vs = map (function (a,(b,c)) -> (ccform1 a, ccform1 b, ccform1 c)) vs in
    (b,vs,i);;

(*
string_of_tm ( (List.nth (getprefix "HJKDESR4") 0).ineq );;
*)

(* generate cfsqp code of ineq *)

let case i j = Printf.sprintf "case %d: *ret = (%s); break;" j (List.nth i j);;

let vardecl y vs = 
  let varname = map (fun (a,b,c) -> b) vs in
  let nvs = List.length vs in
  let  v j = Printf.sprintf "double %s = %s[%d];"   (List.nth varname j) y j in
    join_lines (map v (0-- (nvs-1)));;

let bounds f vs = 
  let lbs = map f vs in
  join_comma lbs;;

let rec geteps = 
  let getepsf = function
    Eps t -> t
    | _ -> 0.0
  in function
      [] -> 0.0
  | b::bs -> max(getepsf b) (geteps bs);;

let cfsqp_code outs trialcount iqd = 
  let (b,vs,i) = cc_of_tm iqd.ineq in
  let eps = geteps (iqd.tags) in 
  let nvs = List.length vs in
  let ni = List.length i in
  let y = "y_mangle__" in 
  let p = Printf.sprintf in
  let s = join_lines ([
    p"// This code is machine generated ";
    p"#include <iomanip.h>\n#include <iostream.h>\n#include <math.h>";
    p"#include \"../Minimizer.h\"\n#include \"../numerical.h\"";
   p"class trialdata { public:   trialdata(Minimizer M,char* s) {     M.coutReport(s);  };};";
  p"int trialcount = %d;\n"  trialcount;
  join_lines(map ccfunction (!notbuiltin));
   p"void c0(int numargs,int whichFn,double* %s, double* ret,void*) {" y;
  vardecl y vs ;
  p"switch(whichFn) {";
  ] @ map (case i) (1-- (-1 + List.length i)) @ [
  p"default: *ret = 0; break; }}\n\n";
  p"void t0(int numargs,int whichFn,double* %s, double* ret,void*) { " y;
  vardecl y vs ;
  p"*ret = (%e) + (%s);" eps (List.nth i 0);
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
    p"//Mathematica generated test data";
    p" assert(near (pi(),4.0*atan(1.0)));";
    p" assert(near (sqrt2(),1.41421356237309));";
    p" assert(near (sqrt8(),2.828427124746190));";
p" assert(near (sol0(),0.5512855984325308));";
p" assert(near (tau0(),1.54065864570856));";
p" assert(near (acos(0.3),1.26610367277949));";
p"assert(near(hminus(),1.2317544220903216));";
p"assert(near(hplus(),1.3254));";
p"assert(near(mm1(),1.012080868420655));";
p"assert(near(mm2(),0.0254145072695089));";
p"assert(near(real_pow(1.18,2.),1.3924));";
p"assert(near(marchal_quartic(1.18),0.228828103048681825));";
p"assert(near(lmfun(1.18),0.30769230769230793));";
p"assert(near(rad2_x(4.1,4.2,4.3,4.4,4.5,4.6),1.6333363881302794));";
p"assert(near(dih_y(2.1,2.2,2.3,2.4,2.5,2.6),1.1884801338917963));";
p"assert(near(sol_y(2.1,2.2,2.3,2.4,2.5,2.6), 0.7703577405137815));";
p"assert(near(ups_x(4.1,4.2,4.3), 52.88));";
p"assert(near(eta_y(2.1,2.2,2.3), 1.272816758217772));";
p"assert(near(beta_bump_force_y(2.1,2.2,2.3,2.4,2.5,2.6), -0.04734449962124398));";
p"assert(near(beta_bump_force_y(2.5,2.05,2.1,2.6,2.15,2.2), beta_bump_y(2.5,2.05,2.1,2.6,2.15,2.2)));";
p"}\n\n";
    ]) in
    Printf.fprintf outs "%s" s;;  

(*
  [sol0;tau0;hplus;mm1;mm2;marchal_quartic;Sphere.vol_x;Sphere.sqrt8;Sphere.sqrt2];;
*)

    
let mk_cfsqp tmpfile iqd = 
  let outs = open_out tmpfile in
  let _ = cfsqp_code outs 500 iqd in
   close_out outs ;;
  (*    Sys.command(sprintf "cat %s" tmpfile);;  *)

let cfsqp_dir = flyspeck_dir^"/../cfsqp";;

let test_ineq idq = 
  let _ =  mk_cfsqp (cfsqp_dir ^ "/tmp/t.cc") idq in
  let _ = Sys.command("cd "^flyspeck_dir^"/../cfsqp; make tmp/t.o") in
    Sys.command(cfsqp_dir^"/tmp/t.o");;
