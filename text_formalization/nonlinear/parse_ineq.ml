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
flyspeck_needs "general/sphere.hl";;
flyspeck_needs "nonlinear/main.hl";;


module Parse_ineq = struct 



  open Sphere;; 

let trialcount = ref 500;;

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
  | "real_of_num" -> let [a] = xs in soh a  (* string_of_num' (dest_numeral a) *)
  | "NUMERAL" -> let [a] = xs in string_of_num' (dest_numeral t)
  | "<" -> let [a;b] = xs in "(" ^ soh a ^ " < " ^ soh b ^ ")"
  | ">" -> let [a;b] = xs in "(" ^ soh a ^ " > " ^ soh b ^ ")"
  | "+" -> let [a;b] = xs in "(" ^ soh a ^ " + " ^ soh b ^ ")"
  | "*" -> let [a;b] = xs in "(" ^ soh a ^ " * " ^ soh b ^ ")"
  | "DECIMAL" ->  string_of_num' (dest_decimal t)
  | "COND" -> let [a;b;c] = xs in "( "^ soh a ^ " ? " ^ soh b ^ " : " ^ soh c ^ ")" 
  | "atn2"      -> let [ab] = xs in let (a,b) = dest_pair ab in  
         "(atn2( " ^ soh a ^ "," ^ soh b ^ "))" 
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

(* solve delta_y y1 y2 y3 y4 y5 y6 = 0 for y4, The negative sign in edge_flat makes the 
   leading coefficient positive *)

let edge_flat =  new_definition`edge_flat y1 y2 y3 y5 y6 = 
 sqrt(quadratic_root_plus (abc_of_quadratic (
   \x4.  -- delta_x (y1*y1) (y2*y2)  (y3*y3)  x4 (y5*y5)  (y6*y6))))`;;

let abc_quadratic = prove (`abc_of_quadratic (\x. a * (x pow 2) + b * x + c) = (a,b,c)`,
 REWRITE_TAC[abc_of_quadratic] THEN
 (REPEAT LET_TAC) THEN
 REWRITE_TAC[PAIR_EQ] THEN
 REPEAT(FIRST_X_ASSUM MP_TAC)THEN
 ARITH_TAC);;

let delta_quadratic = prove( `-- delta_x x1 x2 x3 x4 x5 x6 = 
  (x1) * (x4 pow 2) + (x1*x1 + (x3 - x5)*(x2 - x6) - x1*(x2 + x3 + x5 + x6)) * x4 
   + ( x1*x3*x5 + x1*x2*x6 - x3*(x1 + x2 - x3 + x5 - x6)*x6 - x2*x5*(x1 - x2 + x3 - x5 + x6) ) `,
REWRITE_TAC[delta_x] THEN
ARITH_TAC);;

let edge_flat_rewrite = 
 REWRITE_RULE[abc_quadratic;quadratic_root_plus;delta_quadratic] edge_flat;;

(* function calls are dealt with three different ways:
      - native_c: use the native C code definition of the function. 
      - autogen: automatically generate a C style function from the formal definition.
      - macro_expand: macro expansion; use rewrites to eliminate the function call entirely.
*)

(* Native is  the default case.  There is no need to list them, except as documentation. *)

let native_c = [",";"BIT0";"BIT1";"CONS";"DECIMAL"; "NIL"; "NUMERAL"; "_0"; "acs";"dih_y";
    "ineq";  "pi"; "real_add"; "real_div";"real_pow";
    "real_ge"; "real_mul"; "real_of_num"; "real_sub"; "sol_y";"hminus";
    "lmfun";"wtcount3_y";
    "wtcount6_y";"beta_bump_y";"machine_eps";"cos"
    ];;

let strip_let_tm t = snd(dest_eq(concl(REDEPTH_CONV let_CONV t)));;
let strip_let t = REWRITE_RULE[REDEPTH_CONV let_CONV (concl t )] t;;

(* Auto generate these function definitions in C *)

let autogen = ref[];;

autogen :=map (function b -> snd(strip_forall (concl (strip_let b))))
  [sol0;tau0;hplus;mm1;mm2;vol_x;sqrt8;sqrt2;rho_x;
   rad2_x;ups_x;eta_x;eta_y;norm2hh;arclength;regular_spherical_polygon_area;
 beta_bump_force_y;  a_spine5;b_spine5;beta_bump_lb;marchal_quartic;vol2r;
 Cayleyr.cayleyR;tame_table_d;delta_x4;edge_flat_rewrite];;


(* remove these entirely before converting to C *)

let y_of_x_e = prove(`!y1 y2 y3 y4 y5 y6. y_of_x f y1 y2 y3 y4 y5 y6 =
     f (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)`,
     REWRITE_TAC[y_of_x]);;

let vol_y_e = prove(`!y1 y2 y3 y4 y5 y6. vol_y y1 y2 y3 y4 y5 y6 = 
    y_of_x vol_x y1 y2 y3 y4 y5 y6`,
    REWRITE_TAC[vol_y]);;



let macro_expand = ref [];; 
macro_expand := [gamma4f;vol4f;y_of_x_e;vol_y_e;vol3f;vol3r;vol2f;gamma3f;gamma23f;REAL_MUL_LZERO;
   REAL_MUL_RZERO;FST;SND;pathL;pathR];;
!macro_expand;;

let prep_term t = 
  let t' = REWRITE_CONV (!macro_expand) (strip_let_tm t) in
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

let cfsqp_code outs iqd = 
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
  p"int trialcount = %d;\n"  (!trialcount);
  join_lines(map ccfunction (!autogen));
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
p"assert(near(lmfun(1.27),0.0));";
p"assert(near(rad2_x(4.1,4.2,4.3,4.4,4.5,4.6),1.6333363881302794));";
p"assert(near(dih_y(2.1,2.2,2.3,2.4,2.5,2.6),1.1884801338917963));";
p"assert(near(sol_y(2.1,2.2,2.3,2.4,2.5,2.6), 0.7703577405137815));";
p"assert(near(ups_x(4.1,4.2,4.3), 52.88));";
p"assert(near(eta_y(2.1,2.2,2.3), 1.272816758217772));";
p"assert(near(beta_bump_force_y(2.1,2.2,2.3,2.4,2.5,2.6), -0.04734449962124398));";
p"assert(near(beta_bump_force_y(2.5,2.05,2.1,2.6,2.15,2.2), beta_bump_y(2.5,2.05,2.1,2.6,2.15,2.2)));";
p"assert(near(atn2(1.2,1.3),atan(1.3/1.2)));";
p"assert(near(edge_flat(2.1,2.2,2.3,2.5,2.6),4.273045018670291));";
p"}\n\n";
    ]) in
    Printf.fprintf outs "%s" s;;  

    
let mk_cfsqp tmpfile iqd = 
  let outs = open_out tmpfile in
  let _ = cfsqp_code outs iqd in
   close_out outs ;;

let cfsqp_dir = flyspeck_dir^"/../cfsqp";;
let err = "/tmp/erroruiopiu.txt";;

let compile () = 
  let e = Sys.command("cd "^flyspeck_dir^"/../cfsqp; make tmp/t.o >& "^err) in
  let _ =   (e=0) or (Sys.command ("cat "^err); failwith "compiler error") in
    ();;

 let execute_cfsqp idq = 
  let _ =  mk_cfsqp (cfsqp_dir ^ "/tmp/t.cc") idq in
  let _ = compile() in 
  let _ = (0=  Sys.command(cfsqp_dir^"/tmp/t.o")) or failwith "execution error" in
    ();;

end;;
