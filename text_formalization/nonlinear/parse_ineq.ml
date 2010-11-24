(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Chapter: nonlinear inequalities                                                             *)
(* Author:  Thomas Hales starting from Roland Zumkeller's ccform function    *)
(* Date: 2010-05-09                                                    *)
(* ========================================================================== *)

(* 
   code to generate a c++ file to test
   a nonlinear inequality with cfsqp.

   There are three output files
   /tmp/cfsqp_err.txt, 
   tmp/t.cc tmp/t.o (in the cfsqp directory)
*)

flyspeck_needs "general/sphere.hl";;
flyspeck_needs "nonlinear/ineq.hl";;


module Parse_ineq = struct 

  open Sphere;; 

let trialcount = ref 500;;

let dest_decimal x = match strip_comb x with
    | (dec,[a;b]) ->                     div_num (dest_numeral a) (dest_numeral b)
    | _ -> failwith ("dest_decimal: '" ^ string_of_term x ^ "'") ;;

let string_of_num' x = string_of_float (float_of_num x);; 

let unsplit d f = function
  | (x::xs) ->  List.fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

let join_comma  = unsplit "," (fun x-> x);;

let join_lines  = unsplit "\n" (fun x-> x);;

let join_space  = unsplit " " (fun x-> x);;

let strip_let_tm t = snd(dest_eq(concl(REDEPTH_CONV let_CONV t)));;

let strip_let t = REWRITE_RULE[REDEPTH_CONV let_CONV (concl t )] t;;

let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);; 
(* from HOL Light lib.ml *)

let rec nub = function (* from lpproc.ml *)
  | [] -> []
  | x::xs -> x::filter ((<>) x) (nub xs);;

let output_string tmpfile a = 
  let outs = open_out tmpfile in
  let _ = try (Printf.fprintf outs "%s" a) 
  with _ as t -> (close_out outs; raise t) in
   close_out outs ;;

(* start parsing routines *)

let c_string_of_term t = 
 let rec ccform t =
  let soh = ccform in
  if is_var t then fst (dest_var t) else
  let (f,xs) = strip_comb t in
  let ifix i = let [a;b] = xs in "(" ^ soh a ^ " " ^ i ^ " " ^ soh b ^ ")" in
  let ifix_swapped i = let [b;a] = xs in "(" ^ soh a ^ " " ^ i ^ " " ^ soh b ^ ")" in
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
  | "real_of_num" -> let [a] = xs in soh a  
  | "NUMERAL" -> let [a] = xs in string_of_num' (dest_numeral t)
  | "<" -> let [a;b] = xs in "(" ^ soh a ^ " < " ^ soh b ^ ")"
  | ">" -> let [a;b] = xs in "(" ^ soh a ^ " > " ^ soh b ^ ")"
  | "+" -> let [a;b] = xs in "(" ^ soh a ^ " + " ^ soh b ^ ")"
  | "*" -> let [a;b] = xs in "(" ^ soh a ^ " * " ^ soh b ^ ")"
  | "DECIMAL" ->  string_of_num' (dest_decimal t)
  | "COND" -> let [a;b;c] = xs in "( "^ soh a ^ " ? " ^ soh b ^ " : " ^ soh c ^ ")" 
  | "atn2"      -> let [ab] = xs in let (a,b) = dest_pair ab in  
         "(atn2( " ^ soh a ^ "," ^ soh b ^ "))" 
  | s -> "(" ^ s ^ "(" ^ join_comma(map soh xs) ^ "))" in
   try (ccform t) with Failure s -> failwith (s^" .......   "^string_of_term t);;

let constant_names i =
  let rec cn b =function
    | Const (s,_) -> s::b
    | Comb (s,t) -> (cn [] s) @ (cn[] t) @ b
    | Abs(x,t) -> (cn b t)
    | _ -> b in
  nub (sort (<) (cn [] i ));;


(* Rewrite unusual terms to prepare for C++ conversion *)


let abc_quadratic = prove (`abc_of_quadratic (\x. a * (x pow 2) + b * x + c) = (a,b,c)`,
 REWRITE_TAC[abc_of_quadratic] THEN
 (REPEAT LET_TAC) THEN
 REWRITE_TAC[PAIR_EQ] THEN
 REPEAT(FIRST_X_ASSUM MP_TAC)THEN
 ARITH_TAC);;

let delta_quadratic = prove( `-- delta_x x1 x2 x3 x4 x5 x6 = 
  (x1) * (x4 pow 2) + (x1*x1 + (x3 - x5)*(x2 - x6) 
   - x1*(x2 + x3 + x5 + x6)) * x4 
   + ( x1*x3*x5 + x1*x2*x6 - x3*(x1 + x2 - x3 + x5 - x6)*x6 
    - x2*x5*(x1 - x2 + x3 - x5 + x6) ) `,
REWRITE_TAC[delta_x] THEN
ARITH_TAC);;

let edge_flat_rewrite = 
 REWRITE_RULE[abc_quadratic;delta_quadratic] edge_flat;;

let enclosed_rewrite = 
  REWRITE_RULE[abc_quadratic] 
  (strip_let(REWRITE_RULE[Mur.muRa;Cayleyr.cayleyR_quadratic] Enclosed.enclosed));;

let quadratic_root_plus_curry = 
  new_definition `quadratic_root_plus_curry a b c = quadratic_root_plus (a,b,c)`;;

let quad_root_plus_curry = 
  REWRITE_RULE[quadratic_root_plus] quadratic_root_plus_curry;;

let y_of_x_e = prove(`!y1 y2 y3 y4 y5 y6. y_of_x f y1 y2 y3 y4 y5 y6 =
     f (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)`,
     REWRITE_TAC[y_of_x]);;

let vol_y_e = prove(`!y1 y2 y3 y4 y5 y6. vol_y y1 y2 y3 y4 y5 y6 = 
    y_of_x vol_x y1 y2 y3 y4 y5 y6`,
    REWRITE_TAC[vol_y]);;

let rad2_y_e = prove(`!y1 y2 y3 y4 y5 y6. rad2_y y1 y2 y3 y4 y5 y6 = 
    y_of_x rad2_x y1 y2 y3 y4 y5 y6`,
    REWRITE_TAC[rad2_y]);;


(* function calls are dealt with three different ways:
      - native_c: use the native C code definition of the function. 
      - autogen: automatically generate a C style function from the formal definition.
      - macro_expand: macro expansion; use rewrites to eliminate the function call entirely.
*)

(* Native is the default case.  There is no need to list them, except
   as documentation. *)

let native_c = [
  ",";"BIT0";"BIT1";"CONS";"DECIMAL"; "NIL"; "NUMERAL"; "_0"; "acs";
  "ineq";  "pi"; "adodec"; "bdodec";"real_add"; "real_div";"real_pow";"cos";
  "real_ge"; "real_mul"; "real_of_num"; "real_sub"; "machine_eps";
  (* -- *)
  "sol_y";"dih_y";
  "lmfun";"lnazim";"hminus";
  "wtcount3_y";"wtcount6_y";"beta_bump_y";"matan";
  ];;

let autogen = ref[];;

autogen :=map (function b -> snd(strip_forall (concl (strip_let b))))
  [sol0;tau0;hplus;mm1;mm2;vol_x;sqrt8;sqrt2;sqrt3;rho_x;
   rad2_x;ups_x;eta_x;eta_y;volR; (* solRy;dihRy; *)
   norm2hh;arclength;regular_spherical_polygon_area;
   beta_bump_force_y;  a_spine5;b_spine5;beta_bump_lb;marchal_quartic;vol2r;
   tame_table_d;delta_x4;quad_root_plus_curry;
   edge_flat_rewrite;const1;taum;flat_term;
   taum_y1;taum_y2;taum_y1_y2;arclength_y1;arc_hhn;asn797k;asnFnhk;
   lfun_y1;arclength_x_123;acs_sqrt_x1_d4;acs_sqrt_x2_d4;
   tauq;enclosed_rewrite;
   sol_euler_x_div_sqrtdelta;
   dih_x_div_sqrtdelta_posbranch;
   surfR;surfRy;surfRdyc2;surfy;dih4_y;dih5_y;dih6_y;
   ];;

(*
let macro_expand = ref [];; 
*)

let get_macro_expand() = (
   [gamma4f;vol4f;y_of_x_e;vol_y_e;rad2_y_e;vol3f;vol3r;vol2f;delta4_y;
   gamma3f;gamma23f; (* gamma23f_126_w1;gamma23f_red; *)
   gamma23f_red_03;gamma23f_126_03;
   GSYM quadratic_root_plus_curry;REAL_MUL_LZERO;
   REAL_MUL_RZERO;FST;SND;pathL;pathR;node2_y;node3_y;
   rhazim2;rhazim3;rotate2;rotate3;rotate4;rotate5;rotate6;
		       sol_euler345_x_div_sqrtdelta;
		       sol_euler156_x_div_sqrtdelta;
		       sol_euler246_x_div_sqrtdelta;
		       ldih_x_div_sqrtdelta_posbranch;
		       ldih2_x_div_sqrtdelta_posbranch;
		       ldih2_x_div_sqrtdelta_posbranch;
		      ldih3_x_div_sqrtdelta_posbranch;
		      ldih5_x_div_sqrtdelta_posbranch;
		      ldih6_x_div_sqrtdelta_posbranch;
		      lmdih_x_div_sqrtdelta_posbranch;
		      lmdih3_x_div_sqrtdelta_posbranch;
		      lmdih5_x_div_sqrtdelta_posbranch;
   ] @ (!Ineq.dart_classes));;
   (* dart categories 
   Ineq.dart_std3;Ineq.dartX;Ineq.dartY;Ineq.dart4_diag3;Ineq.apex_flat;
   Ineq.apexfA;Ineq.apexffA;Ineq.apexf4;Ineq.apexff4;Ineq.apexf5;Ineq.apexff5];;
   *)

let prep_term t = 
  let t' = REWRITE_CONV (get_macro_expand()) (strip_let_tm t) in
  let (a,b)=  dest_eq (concl t') in
    b;;

let cc_function t = 
  let args xs = 
    let ls = map (fun s -> "double "^s) xs in join_comma ls in
  let (lhs,rhs) = dest_eq (prep_term t) in
  let (f,xs) = strip_comb lhs in
  let ss = map c_string_of_term xs in
  let p = Printf.sprintf in
  let s = join_lines [
     p"double %s(" (fst (dest_const f)); args ss;
     p") { \nreturn ( %s ); \n}\n\n"  (c_string_of_term rhs);
     ]
  in s;;

let dest_ineq ineq = 
  let t = snd(strip_forall (prep_term (ineq))) in
  let (vs,i) = dest_comb t in
  let (_,vs) = dest_comb vs in
  let vs = dest_list vs in
  let vs = map (fun t -> let (a,b) = dest_pair t in (a,dest_pair b)) vs in
  let vs = map (fun (a,(b,c)) -> (a, b, c)) vs in
    (t,vs,disjuncts i);;

let c_dest_ineq ineq = 
  let cs = c_string_of_term in
  let (b,vs,i) = dest_ineq ineq in
    (cs b, map (fun (a,b,c) -> (cs a, cs b,cs c)) vs,map cs i);;

(* generate c++ code of ineq *)

let case p i j = Printf.sprintf "case %d: *ret = (%s) - (%s); break;" j (List.nth i j) p;;

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

let (has_penalty,penalty) = 
  let penalties iqd =  filter (function Penalty _ -> true | _ -> false) iqd.tags in
  let hasp iqd = (List.length (penalties iqd) >0) in
  let onep iqd = if (hasp iqd) then hd(penalties iqd) else Penalty (0.0,0.0) in
  (hasp,onep);;

let penalty_var iqd = 
   let penalty_ub = function Penalty(a,_) -> string_of_float a in
   ["0.0","penalty",penalty_ub (penalty iqd)];;

let penalty_wt iqd = if has_penalty iqd then
  match (penalty iqd) with
      Penalty(_,b) -> (string_of_float b)^" * penalty" 
else "0.0";;

let cc_main =  
"int main(){
  //Mathematica generated test data
  assert(near (pi(),4.0*atan(1.0)));
  assert(near (sqrt2(),1.41421356237309));
  assert(near (sqrt8(),2.828427124746190));
  assert(near (sol0(),0.5512855984325308));
  assert(near (tau0(),1.54065864570856));
  assert(near (acos(0.3),1.26610367277949));
  assert(near(hminus(),1.2317544220903216));
  assert(near(hplus(),1.3254));
  assert(near(mm1(),1.012080868420655));
  assert(near(mm2(),0.0254145072695089));
  assert(near(real_pow(1.18,2.),1.3924));
  assert(near(marchal_quartic(1.18),0.228828103048681825));
  assert(near(lmfun(1.18),0.30769230769230793));
  assert(near(lmfun(1.27),0.0));
  assert(near(rad2_x(4.1,4.2,4.3,4.4,4.5,4.6),1.6333363881302794));
  assert(near(dih_y(2.1,2.2,2.3,2.4,2.5,2.6),1.1884801338917963));
  assert(near(sol_y(2.1,2.2,2.3,2.4,2.5,2.6), 0.7703577405137815));
  assert(near(sol_y(2, 2, 2, 2.52, 3.91404, 3.464),4.560740765722419));
  assert(near(taum(2.1,2.2,2.3,2.4,2.5,2.6),tau_m(2.1,2.2,2.3,2.4,2.5,2.6) ));
  assert(near(taum(2.1,2.2,2.3,2.4,2.5,2.6),tau_m_alt(2.1,2.2,2.3,2.4,2.5,2.6) ));
  assert(near(taum(2.1,2.2,2.3,2.4,2.5,2.6),0.4913685097602183));
  assert(near(taum(2, 2, 2, 2.52, 3.91404, 3.464),4.009455167289888));
  assert(near(ups_x(4.1,4.2,4.3), 52.88));
  assert(near(eta_y(2.1,2.2,2.3), 1.272816758217772));
  assert(near(beta_bump_force_y(2.1,2.2,2.3,2.4,2.5,2.6), 
    -0.04734449962124398));
  assert(near(beta_bump_force_y(2.5,2.05,2.1,2.6,2.15,2.2), 
    beta_bump_y(2.5,2.05,2.1,2.6,2.15,2.2)));
  assert(near(atn2(1.2,1.3),atan(1.3/1.2)));
  assert(near(edge_flat(2.1,2.2,2.3,2.5,2.6),4.273045018670291));
  assert(near(flat_term(2.1),-0.4452691371955056));
  assert(near(enclosed(2.02,2.04,2.06,2.08,2.1,2.12,2.14,2.16,2.18), 
    3.426676872737882));
}\n\n";;

let cc_code outs iqd = 
  let (b,vs,i) = c_dest_ineq iqd.ineq in
  let vs = vs @ if (has_penalty iqd) then penalty_var iqd else [] in
  let eps = geteps (iqd.tags) in 
  let casep = if has_penalty iqd then "max(0.0,penalty)" else "0.0" in
  let nvs = List.length vs in
  let ni = List.length i in
  let y = "y_mangle__" in 
  let p = Printf.sprintf in
  let s = join_lines ([
    p"// This code is machine generated ";
    p"#include <iomanip.h>\n#include <iostream.h>\n#include <math.h>";
    p"#include \"../Minimizer.h\"\n#include \"../numerical.h\"";
    p"class trialdata { public: trialdata(Minimizer M,char* s) { M.coutReport(s); };};";
    p"int trialcount = %d;\n"  (!trialcount);
    join_lines(map cc_function (!autogen));
    p"void c0(int numargs,int whichFn,double* %s, double* ret,void*) {" y; 
    vardecl y vs ;
    p"switch(whichFn) {";
    ] @ map (case casep i) (1-- (-1 + List.length i)) @ [
    p"default: *ret = 0; break; }}\n\n";
    p"void t0(int numargs,int whichFn,double* %s, double* ret,void*) { " y;  
    vardecl y vs ;
    p"*ret = (%e) + (%s) + (%s);" eps (List.nth i 0) (penalty_wt iqd);
    p"}";
    p"Minimizer m0() {";
    p"  double xmin[%d]= {" nvs;(bounds (function (a,b,c) -> a) vs); 
    p "};\n  double xmax[%d]= {" nvs; (bounds (function (a,b,c) -> c) vs); 
    p "};\n	Minimizer M(trialcount,%d,%d,xmin,xmax);" nvs (ni-1);
    p"	M.func = t0;";
    p"	M.cFunc = c0;";
    p"	return M;";
    p"}";
    p "trialdata d0(m0(),\"%s\");\n\n"  iqd.id;
    p"int near(double x,double y) { double eps = 1.0e-8; return (mabs(x-y)<eps); }";
    ]) in
  Printf.fprintf outs "%s %s" s cc_main;;  

let mk_cc tmpfile iqd = 
  let outs = open_out tmpfile in
  let _ = cc_code outs iqd in
   close_out outs ;;

let compile () = 
  let err = "/tmp/cfsqp_err.txt" in
  let e = Sys.command("cd "^flyspeck_dir^"/../cfsqp; make tmp/t.o >& "^err) in
  let _ =   (e=0) or (Sys.command ("cat "^err); failwith "compiler error") in
    ();;

 let execute_cfsqp idq = 
  let cfsqp_dir = flyspeck_dir^"/../cfsqp" in
  let _ =  mk_cc (cfsqp_dir ^ "/tmp/t.cc") idq in
  let _ = compile() in 
  let _ = (0=  Sys.command(cfsqp_dir^"/tmp/t.o")) or failwith "execution error" in
    ();;

 let execute_cfsqp_list xs = 
      for i=0 to (List.length xs - 1) 
      do  execute_cfsqp (List.nth xs i); Sys.command("date") done;;

(* new section glpk code generation *)

  let yy6 =  [`y1:real`;`y2:real`;`y3:real`;`y4:real`;`y5:real`;`y6:real`];;
  let yy9 = yy6 @ [`y7:real`;`y8:real`;`y9:real`];;

  let  translate =ref 
     [("dih_y","azim[i,j]");("dih2_y","azim2[i,j]");("dih3_y","azim3[i,j]");("sol_y","sol[j]");
    ("taum","tau[j]");("tauq","tau[j]");("rhazim","rhazim[i,j]");
    ("rhazim2","rhazim2[i,j]");("rhazim3","rhazim3[i,j]");("sqrt8","sqrt8")];;

  let reverse = 
     let xs =     [("y2","y3");("y5","y6");("rhazim2","rhazim3");
      ("dih2_y","dih3_y");] in
     let f (a,b) = (b,a) in
     let ys =     xs @ map f xs in
       fun s -> try (List.assoc s ys) with Not_found -> s;;

  let glpk_lookup rev s xs =
    let s' = if rev then reverse s else s in
    if (xs = yy6) or (xs = yy9) then
      try (List.assoc s' (!translate)) with Not_found -> failwith ("glpk_lookup translate" ^ s)
    else if xs = [] then 
      try (List.assoc s' (!translate)) with Not_found -> (s'^"[i,j]")
    else  failwith ("glpk_lookup unknown arg list:" ^ s);;

 let rec glpk_form rev t =
  let soh = glpk_form rev in
  if is_var t then glpk_lookup rev (fst (dest_var t)) [] else
  let (f,xs) = strip_comb t in
  let ifix i = let [a;b] = xs in "(" ^ soh a ^ " " ^ i ^ " " ^ soh b ^ ")" in
  let ifix_swapped i = let [b;a] = xs in "(" ^ soh a ^ " " ^ i ^ " " ^ soh b ^ ")" in
  (if not (is_const f) then failwith ("glpk constant expected: " ^ string_of_term f));
  match fst (dest_const f) with
  | "real_gt" | "real_ge" | "real_sub" -> ifix "-"
  | "real_lt" | "real_le" -> ifix_swapped "-"
  | "real_add" -> ifix "+"
  | "real_mul" -> ifix "*"
  | "real_div" -> ifix "/"
  | "real_neg" -> let [a] = xs in "(-" ^ soh a ^ ")"
  | "real_of_num" -> let [a] = xs in soh a  
  | "NUMERAL" -> let [a] = xs in string_of_num' (dest_numeral t)
  | "DECIMAL" ->  string_of_num' (dest_decimal t)
  | s -> "(" ^ glpk_lookup rev s xs^ ")" ;;

let counter = 
      let ineqcounter = ref 0 in
      fun t -> (let u = !ineqcounter in let _ =  ineqcounter := u+1 in u);;

let mk_glpk_ineq rev iqd = 
    let ineq = iqd.ineq in
  let t = snd(strip_forall  (ineq)) in
  let (vs,i) = dest_comb t  in
  let (_,vs) = dest_comb vs in
  let (f,xs) = strip_comb vs in
  let (dart,_) = dest_const f in
  let i' = hd(disjuncts i) in
  let _ = (xs = yy6) or (xs = yy9) or (print_qterm vs; failwith "dart_class y1 ... y6 expected") in
  let p = Printf.sprintf in
  let s =   p"ineq%d 'ID[%s]' \n  { (i,j) in %s } : \n  %s >= 0.0;\n\n" 
    (counter()) iqd.id dart (glpk_form rev i') in
    s;;

let mk_glpk_ineq_id rev s = 
  let iqd = Ineq.getexact s in mk_glpk_ineq rev (hd iqd);;

let test_domain_symmetry idq = 
  let ineq = idq.ineq in
  let dart = List.nth (snd(strip_comb (snd(strip_forall ineq)))) 0 in
  let dom = map(fun (a,(b,c)) -> (a,c)) (map (fun (a,b) -> (a,dest_pair b)) 
     (map dest_pair 
     (dest_list(snd(dest_eq(concl(REWRITE_CONV(!Ineq.dart_classes) dart))))))) in
  let nth = List.nth in
    ((nth dom 1 = nth dom 2) & (nth dom 4 = nth dom 5)) or failwith "domain asym";;

let lpstring() = 
(*  let fil r = filter (can (fun t ->  (find ((=) r) t.tags))) (!Ineq.ineqs) in *)
  let _ = map test_domain_symmetry (Ineq.getfield Lpsymmetry) in
  join_lines 
    ("# File automatically generated from nonlinear inequality list via lpstring().\n\n" ::
    (map (mk_glpk_ineq false) (Ineq.getfield Lp)) @
    ["# Symmetry section\n\n"] @ 
    (map (mk_glpk_ineq true) (Ineq.getfield Lpsymmetry)));;

(* Tex Processing of Inequalities *)

let mk_texstring (tm,id,s) = match tm with
  | Section -> "\\section{"^id^" "^s^"}\n" 
  | Comment -> "\\begin{remark}["^id^"]\n"^s^"\n\\end{remark}\n"
  | Ineqdoc -> "\\begin{calculation}["^id^"]\n"^s^"\n\\end{calculation}\n";;

let texstring() = join_lines (map mk_texstring (List.rev (!Ineq.ineqdoc)));;


(*
output_string "/tmp/ineqdoc.tex" (texstring());;
*)

(* Objective caml processing from ineq *)


let ocaml_string_of_term t = 
 let rec ocaml_form t =
  let soh = ocaml_form in
  let paren s = "("^ s ^")" in
  if is_var t then fst (dest_var t) else
  let (f,xs) = strip_comb t in
  let ifix i = let [a;b] = xs in "(" ^ soh a ^ " " ^ i ^ " " ^ soh b ^ ")" in
  let ifix_swapped i = let [b;a] = xs in "(" ^ soh a ^ " " ^ i ^ " " ^ soh b ^ ")" in
  (if not (is_const f) then failwith ("Oracle error: " ^ string_of_term f));
  match fst (dest_const f) with
  | "real_sub" -> ifix "-. "
  | "real_add" -> ifix "+."
  | "real_mul" -> ifix "*."
  | "real_div" -> ifix "/."
  | "real_neg" -> let [a] = xs in "(-. " ^ soh a ^ ")"
  | "acs" -> let [a] = xs in "(acos("^soh a^ "))"
  | "real_of_num" -> let [a] = xs in soh a  
  | "NUMERAL" -> let [a] = xs in string_of_num' (dest_numeral t)
  | "=" -> let [a;b] = xs in soh a ^ " = " ^ soh b
   | "DECIMAL" ->  string_of_num' (dest_decimal t)
  | "atn2"      -> let [ab] = xs in let (a,b) = dest_pair ab in  
         "atan2 " ^ paren(soh b) ^ " " ^ paren(soh a) ^ "  "  (* note reverse order in ocaml *) 
  | s -> " " ^ s ^ " " ^ join_space(map soh xs) ^ " " in
   try (ocaml_form t) with Failure s -> failwith (s^" .......   "^string_of_term t);;

let ocaml_function t = 
  "let " ^ ocaml_string_of_term t ^ ";;\n\n";;

let ocaml_autogen = map (function b -> snd(strip_forall (concl (strip_let b))))
   [sqrt2;sqrt8;delta_x;delta_y;delta_x4;delta_x6;ups_x;eta_x;
    eta_y;dih_x;dih_y;dih2_y;dih3_y;sol_x;sol_y;interp;ly;const1;rho;rhazim;lnazim;taum];;


let ocaml_code = 
  "(* code automatically generated from Parse_ineq.ocaml_code *)\n\n"^
   "module Sphere_math = struct\n\n"^
   "let sqrt = Pervasives.sqrt\n\n" ^
   "let pi = 4.0 *. atan(1.0);;\n" ^
   (join_lines (map ocaml_function ocaml_autogen)) ^
   "end;;\n";;

output_string "/tmp/sphere.ml" ocaml_code;;



end;;
