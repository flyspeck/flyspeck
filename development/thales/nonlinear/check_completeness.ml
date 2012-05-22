(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(* Section: Local Fan Main Estimate                                           *)
(* Chapter: Local Fan                                                         *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2012-05-05                                                           *)
(* ========================================================================== *)

(* 
Check completeness (informally) 
of case anaysis in proof of Kepler conjecture, Main Estimate.

The purpose is to transform the list init_cs into terminal_cs
in a finite sequence of regulated moves.
*)


#directory "/Users/thomashales/Desktop/googlecode/hol_light";;
#use "hol.ml";;

flyspeck_needs "../glpk/sphere.ml";;
(*
****************************************
BASICS
****************************************
*)


let false_on_fail b x = try (b x) with _ -> false;;

let filter_some xs = 
  mapfilter (function |Some x -> x |None -> failwith "none" ) xs;;

let length = List.length;;

let nub = Lib.uniq;;

let sortuniq xs = uniq (Lib.sort (<) xs);;

let psort (i,j) = (min i j),(max i j);;

let rec cart a b = 
  match a with
    | [] -> []
    | a::rest -> (map (fun x -> (a,x)) b) @ cart rest b;;

let cart2 a = cart a a;;


(* from parse_ineq *)
let unsplit d f = function
  | (x::xs) ->  List.fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

let join_comma  = unsplit "," (fun x-> x);;
let join_semi  = unsplit ";" (fun x-> x);;
let join_lines  = unsplit "\n" (fun x-> x);;
let join_space  = unsplit " " (fun x-> x);;

let string_of_list f xs = 
  let ss = map f xs in
   "["^(join_semi ss)^"]";;

let string_of_pair (i,j) = 
    Printf.sprintf "(%d,%d)" i j;;

let string_of_triple (i,j,s) = 
  Printf.sprintf "(%d,%d,%3.2f)" i j s;;

let string_of_f f k = 
  let ks = filter (fun (i,j) -> i<j) (cart2 (0--(k-1))) in
  let g (i,j) = (i,j,f i j) in
    string_of_list string_of_triple (map g ks);;

let arc = Sphere_math.arclength;;  (* in glpk directory *)
let sqrt = Pervasives.sqrt;;
let cos  = Pervasives.cos;;

(* a few constants.  We do tests of exact equality on floats,
   but this should work because we never do arithmetic on floats
   after initialization, so there is no source of roundoff error
   after initialization. *)

let zero = 0.0;;
let target = 1.541;;
let two = 2.0;;
let twoh0 = 2.52;;
let sqrt8 = Pervasives.sqrt(8.0);;
let three = 3.0;;
let cstab = 3.01;;
let four = 4.0;;
let fourh0 = 2.0 *. twoh0;;
let upperbd = 6.0;;  (* 6.0 > 4 * h0, upper bound on diags in BB *)

let tame_table_d0 i = 
  if (i <= 3) then zero
  else if (i=4) then 0.206 
  else if (i=5) then 0.4819
  else if (i=6) then 0.712
  else target;;

let tame_table_d r s = 
  if (r + 2 * s <= 3) then 0.0
  else
    let r' = float_of_int r in
    let s' = float_of_int s in
      0.103 *. (2.0 -. s') +. 0.2759 *. (r' +. 2.0 *. s' -. 4.0);;


(*
look only at global minumum points for tau*(s,v) (for s fixed)
and such that tau*(s,v)<=0.
Let index(v) = the number of edges st |vi-vj|=a(i,j). 
and such that index(v) is minimized among global minimum points in Bs.
Call this set MM(s) (index-minimizers).

The semantics that guide us will be counterexample propagation;
if an augmented constraint system contains a point, does the
output of the function contain a nonempty augmented constraint system?

Formally, we will prove statements of the form for various 
f:ACS -> (ACS) list
|- nonempty_M cs ==> (?cs'. mem cs'(f cs) /\ nonempty_M cs').
*)

(* DEPRECATED

type attrib_cs =
    Cs_straight of int
  | Cs_lo  of int
  | Cs_hi of int;;

  | Cs_generic
  | Cs_lunar
  | Cs_interior_crit;; 

 Generic and lunar not closed conditions.

 Cs_hi not needed for initial reductions.

 Cs_interior_crit means all index-minimizers v 
  st. all diags are strictly between a and b. 
  Not a closed condition, don't use.

let amap f a = match a with
      | Cs_straight i -> Cs_straight (f i)
      | Cs_lo i -> Cs_lo (f i)
      | Cs_hi i -> Cs_hi (f i);;
*)

type constraint_system = 
{
  k_cs : int;
  d_cs : float;
  a_cs : int->int ->float;
  b_cs: int->int->float;
  am_cs: int->int->float;
  bm_cs: int->int->float;
  js_cs : (int*int) list;
  lo_cs :int list;
  hi_cs : int list;
  str_cs : int list;
  history_cs : string list;
};;

let string_of_cs cs =
  let s = string_of_list string_of_int in
  let k = string_of_int cs.k_cs in
  let d = string_of_float cs.d_cs in
  let a = string_of_f cs.a_cs (cs.k_cs) in
  let b = string_of_f cs.b_cs (cs.k_cs) in
  let am = string_of_f cs.am_cs (cs.k_cs) in
  let bm = string_of_f cs.bm_cs (cs.k_cs) in
  let js = string_of_list string_of_pair cs.js_cs in
  let lo = s cs.lo_cs in
  let hi = s cs.hi_cs in
  let str = s cs.str_cs in
    Printf.sprintf 
      "{\n k=%s;\n d=%s;\n a=%s;\n b=%s;\n am=%s;\n bm=%s;\n js=%s;\n lo=%s;\n hi=%s;\n str=%s;\n}\n"
      k d a b am bm js lo hi str;;

let pp_print_cs f cs = pp_print_string f (string_of_cs cs);;

let report_cs cs = report(string_of_cs cs);;

(* report(string_of_cs quad_std_cs);; *)
(* #install_printer pp_print_cs;; *)


(*
There are B-fields and M-fields.
The B-fields define the domain of the constraint system s.
The M-fields partition the minimizers in B_s.

k,a,b, are the primary B-fields
d,j are secondary B-fields that define the function tau.

lo,hi,str,ma,mb are M-fields.

js represented as pairs (i,j) with i<j and adjacent.
a,b are bounds defining BB_s.

ma,mb do not affect the augmented constraint system s.
The deformation lemmas are all partitioning the M-fields.

Subdivision partitions the B-fields.
Transfer resets the M-fields and changes the B-field.
*)


let modify_cs cs =
  fun ?k:(k=cs.k_cs) ?a:(a=cs.a_cs) ?b:(b=cs.b_cs) 
    ?am:(am=cs.am_cs) ?bm:(bm=cs.bm_cs)
    ?d:(d=cs.d_cs)
      ?js:(js=cs.js_cs) ?lo:(lo=cs.lo_cs) ?hi:(hi=cs.hi_cs)
      ?str:(str=cs.str_cs) ?h:(history=cs.history_cs) () ->
 {
  k_cs = k;
  a_cs = a;
  b_cs = b;
  am_cs = am;
  bm_cs = bm;
  d_cs = d;
  js_cs = js;
  lo_cs = lo;
  hi_cs = hi;
  str_cs = str;
  history_cs = history;
};;

let hist cs s = modify_cs cs ~h:(s::cs.history_cs) ();;

(* usage : modify_cs hex_std_cs ~k:4 ();; *)

let reset_attr cs = 
  modify_cs cs ~am:cs.a_cs ~bm:cs.b_cs ~lo:[] ~hi:[] ~str:[] ();;

let ink k i = (i+1) mod k;;

let dek k i = (i+k-1) mod k;;

let inc cs i = ink cs.k_cs i;;

let dec cs i = dek cs.k_cs i;;

let inka k a = 
    map (ink k) a;;

let mk_j cs i = psort (i,inc cs i);;

let memj cs (i,j) = mem (psort (i,j)) cs.js_cs;;

let ks_cs cs = (0-- (cs.k_cs -1));;

let ks_cart cs = cart2 (ks_cs cs);;

let compact u = length (sortuniq u) = length u;;

let alldiag cs =   
  let ks = ks_cs cs in
  filter (fun (i,j) -> (i<j) && not (inc cs i = j) && not (inc cs j = i))
    (cart2 ks);;


(*
****************************************
BASIC OPS ON CONSTRAINT SYSTEMS
****************************************
*)


let is_cs cs = 
  let f (i,j) = 
    (cs.a_cs i j = cs.a_cs j i) &&
      (cs.b_cs i j = cs.b_cs j i) &&
    (cs.am_cs i j = cs.am_cs j i) &&
      (cs.bm_cs i j = cs.bm_cs j i) &&
      (cs.a_cs i j <= cs.am_cs i j) &&
      (cs.am_cs i j <= cs.bm_cs i j) &&
      (cs.bm_cs i j <= cs.b_cs i j) in
  let ks = ks_cs cs in
  let k2s = cart2 ks in
  let bm = forall f k2s or failwith "is_cs: bm" in
  let bs = ((cs.k_cs <= 6) && (cs.k_cs >= 3)) or failwith "is_cs:bs" in
  let bj = (length cs.js_cs + cs.k_cs <= 6) or failwith "is_cs:bj" in
  let bj' = (compact cs.js_cs) or failwith "is_cs:bj'" in 
  let fj (i,j) = (i < j) && ((inc cs i = j) or (inc cs j = i)) in
  let bj'' = (forall fj cs.js_cs) or failwith "is_cs:bj''" in 
  let ls =  cs.lo_cs @ cs.hi_cs @ cs.str_cs in
    bm && bs && bj && bj' && bj'' && 
      subset ls ks && subset cs.js_cs k2s ;;  

let attr_free cs = 
  let f (i,j) = (cs.a_cs i j = cs.am_cs i j) && (cs.b_cs i j = cs.bm_cs i j) in
  let ks = ks_cs cs in
  let k2s = cart2 ks in
  let bm = forall f k2s or failwith "attr_free" in
    bm && (cs.lo_cs=[]) && (cs.hi_cs=[]) &&(cs.str_cs=[]);;

let zero_diag a xs = forall (fun i -> ((=) zero) (a i i)) xs;;

let is_stable cs =
  let f (i,j) = 
    (i = j) or (2.0 <= cs.a_cs i j) in
  let ks =  ks_cs cs in 
  let k2s = cart2 ks in
  let bm = forall f k2s or failwith "is_st:bm" in 
  let bs = zero_diag cs.a_cs ks or failwith "is_st:bs" in 
  let g i = (cs.b_cs i (inc cs i) <= cstab) in
  let bs' = forall g ks or failwith "is_st:bs'" in 
  let fj (i,j) = not(memj cs (i,j)) or 
    (sqrt8 = cs.a_cs i j && cs.b_cs i j = cstab) in
  let bj = forall fj k2s or failwith "is_st:bj" in 
    bm && bs && bs' && bj;;

let is_tri_stable cs = 
  let bk = (3 = cs.k_cs) or failwith "ts:3" in
  let  f (i,j) = 
    (i = j) or (2.0 <= cs.a_cs i j) in
  let ks =  ks_cs cs in 
  let k2s = cart2 ks in
  let bm = forall f k2s or failwith "ts:bm" in 
  let bs = zero_diag cs.a_cs ks  or failwith "ts:bs" in
  let g i = (cs.b_cs i (inc cs i) < four) in
  let bs' = forall g ks or failwith "ts:bs'" in 
  let fj (i,j) = not(memj cs (i,j)) or 
    (sqrt8 = cs.a_cs i j && cs.b_cs i j = cstab) in
  let bj = forall fj k2s or failwith "ts:bj" in 
    bk && bm && bs && bs' && bj;;

let is_aug_cs cs = 
  let bc = is_cs cs in
  let bs = false_on_fail is_tri_stable  cs or is_stable  cs in
  let bd = (cs.d_cs < 0.9) or failwith "aug:bd" in
  let k2s = ks_cart cs in
  let edge (i,j) = (j = inc cs i) or (i = inc cs i) in
  let fm (i,j) = edge(i,j) && (i < j) && (two < cs.a_cs i j or twoh0< cs.b_cs i j) in
  let m = length (filter fm k2s) in
  let bm = (m + cs.k_cs <= 6) or failwith "aug:bm" in
    bc && bs && bd && bm;;

(* f is an edge preserving map *)

let map_cs f g cs = 
  let ks = ks_cs cs in
  let _ = forall (fun i-> f(g i) = i) ks or failwith "map_cs:not inverse" in
  let _ = forall (fun i-> g(f i) = i) ks or failwith "map_cs:not inverse" in
  let a' a i j = a (f i) (f j) in
  let g2 (i,j) = psort (g i , g j ) in
  {
    k_cs = cs.k_cs;
    d_cs = cs.d_cs;
    a_cs = a' (cs.a_cs);
    b_cs = a' (cs.b_cs);
    am_cs = a' (cs.am_cs);
    bm_cs = a' (cs.bm_cs);
    lo_cs = map g cs.lo_cs;
    hi_cs = map g cs.hi_cs;
    str_cs = map g cs.str_cs;
    js_cs = map g2 cs.js_cs;
    history_cs = cs.history_cs;
  };;

let opposite_cs cs = 
  let f i = (cs.k_cs - (i+1)) in
    map_cs f f cs;;

let rotate_cs cs = map_cs (inc cs) (dec cs) cs;;

let rec rotatek_cs k cs = 
  funpow k rotate_cs cs;;

(* attribute free iso *)

let reset_iso_strict_cs cs cs' = 
  let cs = reset_attr cs in
  let cs' = reset_attr cs' in
  let bk = cs.k_cs = cs'.k_cs in
  let bd = cs.d_cs = cs'.d_cs in
  let m r r' = forall (fun (i,j) -> r i j = r' i j) (ks_cart cs) in
  let ba = m cs.a_cs cs'.a_cs in
  let bb = m cs.b_cs cs'.b_cs in
  let ps js = map psort js in
  let bj = set_eq (ps cs.js_cs) (ps cs'.js_cs) in
    bk && bd && ba && bb && bj;;


let proper_reset_iso_cs cs cs' = 
  Lib.exists (fun i -> reset_iso_strict_cs (rotatek_cs i cs) cs') (ks_cs cs);;

let reset_iso_cs cs cs' = 
  (cs.k_cs = cs'.k_cs) && 
 (  proper_reset_iso_cs cs cs' or proper_reset_iso_cs (opposite_cs cs) cs');;



(*
****************************************
FUNCTION BUILDERS
****************************************
*)

let cs_adj adj diag k i j = 
  let s t = string_of_int t in
  if (i<0) or (j<0) or (i>=k) or (j>=k) 
  then failwith ("adj out of range"^(s k)^(s i)^(s j)) 
  else if (i=j) then zero
  else if (j = ink k i) or (i = ink k j) then adj
  else diag;;

let a_pro pro adj diag k i j = 
  if (i<0) or (j<0) or (i>=k) or (j>=k) then failwith "pro out of range"
  else if (i=j) then zero
  else if (i=0 && j=1) or (j=0 && i=1) then pro
  else if (j = ink k i) or (i = ink k j) then adj
  else diag ;;

(*  BUGGED IF data not sorted:
let funlist data d i j = 
  if (i=j) then zero
  else assocd (psort (i,j)) data d;;
*)

let funlist data = 
  let data' = map (fun ((i,j),d) -> (psort(i,j),d)) data in
    fun d i j ->
      if (i=j) then zero
      else assocd (psort (i,j)) data' d;;

let override a (p,q,d) i j = 
  if psort (p,q) = psort (i,j) then d else a i j;;

let overrides a data =
  let fd = funlist data in
      fun i j ->
	fd (a i j) i j;;

(*
****************************************
TABLES OF AUGMENTED CONSTRAINT SYSTEMS
****************************************
*)

let mk_cs (k,d,a,b,h) = {
  k_cs = k;
  d_cs = d;
  a_cs = a;
  b_cs = b;
  am_cs = a;
  bm_cs = b;
  js_cs = [];
  lo_cs = [];
  hi_cs = [];
  str_cs = [];
  history_cs = [h];
};;

let hex_std_cs = mk_cs (6, tame_table_d0 6,
  cs_adj two twoh0 6,
  cs_adj twoh0 upperbd 6,"hex std init");;

let pent_std_cs = mk_cs (5,tame_table_d0 5,
  cs_adj two twoh0 5,
  cs_adj twoh0 upperbd 5,"pent std init");;

let quad_std_cs = mk_cs (4,tame_table_d0 4,
  cs_adj two twoh0 4,
  cs_adj twoh0 upperbd 4,"quad std init");;

let tri_std_cs = mk_cs (3,tame_table_d0 3,
  cs_adj two twoh0 3,
  cs_adj twoh0 upperbd 3,"tri std init");;

let pent_diag_cs = mk_cs (
   5,
   0.616,
   cs_adj two sqrt8 5,
   cs_adj twoh0 upperbd 5,"pent diag init");;

let quad_diag_cs = mk_cs (
   4,
   0.467,
   cs_adj two three 4,
   cs_adj twoh0 upperbd 4,"quad diag init");;

let pent_pro_cs = mk_cs (
   5,
   0.616,
   a_pro twoh0 two twoh0 5,
   a_pro sqrt8 twoh0 upperbd 5,"pent pro init");;

let quad_pro_cs = mk_cs (
   4,
   0.477,
   a_pro twoh0 two sqrt8 4,
   a_pro sqrt8 twoh0 upperbd 4,"quad pro init");;

let init_cs = [
  hex_std_cs ;
  pent_std_cs ;
  quad_std_cs ;
  tri_std_cs ;
  pent_diag_cs ;
  quad_diag_cs ;
  pent_pro_cs ;
  quad_pro_cs ;
];;

forall is_aug_cs init_cs;;
forall attr_free init_cs;;

(* now for the terminal cases done by interval computer calculation *)

let terminal_hex =
mk_cs (
   6,
   tame_table_d0 6,
   cs_adj two cstab 6,
   cs_adj two upperbd 6,"terminal hex");;

let terminal_pent = 
mk_cs (
   5,
   0.616,
   cs_adj two cstab 5,
   cs_adj two upperbd 5,"terminal");;

(* two cases for the 0.467 bound: all top edges 2 or both diags 3 *)

let terminal_adhoc_quad_9563139965A = 
mk_cs (
   4,
   0.467,
   cs_adj two three 4,
   cs_adj two upperbd 4,"terminal");;

let terminal_adhoc_quad_9563139965B = 
mk_cs (
   4,
   0.467,
   cs_adj two three 4,
   cs_adj twoh0 three 4,"terminal");;

let terminal_adhoc_quad_4680581274 = mk_cs(
 4,
 0.616 -. 0.11,
 funlist [(0,1),cstab ; (0,2),cstab ; (1,3),cstab ] two,
 funlist [(0,1),cstab ; (0,2),upperbd ; (1,3),upperbd ] two,"terminal 4680581274");;

let terminal_adhoc_quad_7697147739 = mk_cs(
 4,
 0.616 -. 0.11,
 funlist [(0,1),sqrt8 ; (0,2),cstab ; (1,3),cstab ] two,
 funlist [(0,1),sqrt8 ; (0,2),upperbd ; (1,3),upperbd ] two,"terminal 7697147739");;

let terminal_tri_3456082115 = mk_cs(
 3,
 0.5518 /. 2.0,
 funlist [(0,1), cstab; (0,2),twoh0; (1,2),two] two,
 funlist [(0,1), 3.22; (0,2),twoh0; (1,2),two] two,"terminal 3456082115");;

let terminal_tri_7720405539 = mk_cs(
 3,
 0.5518 /. 2.0 -. 0.2,
 funlist [(0,1),cstab; (0,2),twoh0; (1,2),two] two,
 funlist [(0,1),3.41; (0,2),twoh0; (1,2),two] two,"terminal 7720405539");;
 
let terminal_tri_2739661360 = mk_cs(
 3,
 0.5518 /. 2.0 +. 0.2,
 funlist [(0,1),cstab; (0,2),cstab; (1,2),two] two,
 funlist [(0,1),3.41; (0,2),cstab; (1,2),two] two,"terminal 2739661360");;
 
let terminal_tri_9269152105 = mk_cs(
 3,
 0.5518 /. 2.0 ,
 funlist [(0,1),3.41; (0,2),cstab; (1,2),two] two,
 funlist [(0,1),3.62; (0,2),cstab; (1,2),two] two,"terminal 9269152105");;

let terminal_tri_4922521904 = mk_cs(
 3,
 0.5518 /. 2.0 ,
 funlist [(0,1),cstab; (0,2),twoh0; (1,2),two] two,
 funlist [(0,1),3.339; (0,2),twoh0; (1,2),two] two,"terminal 4922521904");;

let terminal_quad_1637868761 = mk_cs(
 4,
 0.5518,
 funlist [(0,1),two; (1,2), cstab; 
                  (2,3),twoh0; (0,3),two; (0,2),3.41; (1,3),cstab] two,
 funlist [(0,1),two; (1,2), cstab;
                  (2,3),twoh0; (0,3),two; (0,2),3.634; (1,3),upperbd] two,"terminal 1637868761");;


let ear_cs = 
{
  k_cs = 3;
  d_cs = 0.11;
  a_cs = funlist [(0,1),sqrt8] two;
  b_cs = funlist [(0,1),cstab] twoh0;
  am_cs = funlist [(0,1),sqrt8] two;
  bm_cs = funlist [(0,1),cstab] twoh0;
  js_cs = [0,1];
  lo_cs = [];
  hi_cs = [];
  str_cs = [];
  history_cs= ["ear 3603097872"];
};;

(* consequence of usual ear *)
let ear_jnull = modify_cs ear_cs ~js:[] ();;

let terminal_ear_3603097872 = ear_cs;;


let terminal_tri_5405130650 = 
{
  k_cs = 3;
  d_cs =  0.477 -.  0.11;
  a_cs = funlist [(0,1),sqrt8;(0,2),twoh0;(1,2),two] two;
  b_cs = funlist [(0,1),cstab;(0,2),sqrt8;(1,2),twoh0] twoh0;
  am_cs = funlist [(0,1),sqrt8;(0,2),twoh0;(1,2),two] two;
  bm_cs = funlist [(0,1),cstab;(0,2),sqrt8;(1,2),twoh0] twoh0;
  js_cs = [0,1];
  lo_cs = [];
  hi_cs = [];
  str_cs = [];
  history_cs=["terminal 5405130650"];
};;

let terminal_tri_5766053833 = 
{
  k_cs = 3;
  d_cs =  0.696 -. 2.0 *. 0.11; 
  a_cs = funlist [(0,1),sqrt8;(1,2),sqrt8] two;
  b_cs = funlist [(0,1),cstab;(1,2),cstab] two;
  am_cs = funlist [(0,1),sqrt8;(1,2),sqrt8] two;
  bm_cs = funlist [(0,1),cstab;(1,2),cstab] two;
  js_cs = [(0,1);(1,2)];
  lo_cs = [];
  hi_cs = [];
  str_cs = [];
  history_cs=["terminal 5766053833"];
};;

let terminal_tri_5026777310 = mk_cs(
 3,
  0.6548 -. 2.0 *. 0.11,
 funlist [(0,1),sqrt8;(1,2),sqrt8] two,
 funlist [(0,1),cstab;(1,2),cstab] twoh0,"terminal 5026777310");;

let terminal_tri_7881254908 = mk_cs(
 3,
  0.696 -. 2.0 *. 0.11,
 funlist [(0,1),sqrt8;(1,2),sqrt8] twoh0,
 funlist [(0,1),cstab;(1,2),cstab] twoh0,"terminal 7881254908");;

(* 1107929058 *)
let terminal_std_tri_OMKYNLT_2_1  = mk_cs(
 3,
  tame_table_d 2 1,
 funlist [(0,1),twoh0] two,
 funlist [(0,1),twoh0] two,"terminal 1107929058");;

let terminal_std_tri_7645170609 = mk_cs(
 3,
  tame_table_d 2 1,
 funlist [(0,1),sqrt8] two,
 funlist [(0,1),sqrt8] two,"terminal 7645170609");;

(* 1532755966 *)
let terminal_std_tri_OMKYNLT_1_2  = mk_cs(
 3,
  tame_table_d 1 2,
 funlist [(0,1),two] twoh0,
 funlist [(0,1),two] twoh0,"terminal 1532755966");;

let terminal_std_tri_7097350062 = mk_cs(
 3,
  tame_table_d 1 2 +. (tame_table_d 2 1 -. 0.11),
 funlist [(0,1),twoh0;(0,2),sqrt8] two,
 funlist [(0,1),twoh0;(0,2),sqrt8] two,"terminal 7097350062");;

let terminal_std_tri_2900061606 = mk_cs(
 3,
  tame_table_d 1 2 +. (tame_table_d 2 1 -. 0.11),
 funlist [(0,1),twoh0;(0,2),cstab] two,
 funlist [(0,1),twoh0;(0,2),cstab] two,"terminal 2900061606");;

let terminal_std_tri_2200527225 = mk_cs(
 3,
  tame_table_d 1 2 +. 2.0*. (tame_table_d 2 1 -. 0.11),
 funlist [(0,1),two;] sqrt8,
 funlist [(0,1),two;] sqrt8,"terminal 2200527225");;

let terminal_std_tri_3106201101 = mk_cs(
 3,
  tame_table_d 1 2 +. 2.0*. (tame_table_d 2 1 -. 0.11),
 funlist [(0,1),two;(0,2),cstab] sqrt8,
 funlist [(0,1),two;(0,2),cstab] sqrt8,"terminal 3106201101");;

let terminal_std_tri_9816718044 = mk_cs(
 3,
  tame_table_d 1 2 +. 2.0*. (tame_table_d 2 1 -. 0.11),
 funlist [(0,1),two] cstab,
 funlist [(0,1),two] cstab,"terminal 9816718044");;

let terminal_std_tri_1080462150 = mk_cs(
 3,
  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11),
 funlist [] twoh0,
 funlist [] twoh0,"terminal 1080462150");;

let terminal_std_tri_4143829594 = mk_cs(
 3,
  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11),
 funlist [(0,1),cstab] twoh0,
 funlist [(0,1),cstab] twoh0,"terminal 4143829594");;

let terminal_std_tri_7459553847 = mk_cs(
 3,
  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11),
 funlist [(0,1),twoh0] cstab,
 funlist [(0,1),twoh0] cstab,"terminal 7459553847");;

let terminal_std_tri_4528012043 = mk_cs(
 3,
  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11),
 funlist [] cstab,
 funlist [] cstab,"terminal 4528012043");;

let terminal_std_tri_OMKYNLT_3336871894 = mk_cs(
 3,
 zero,
 funlist [] two,
 funlist [] two,"terminal 3336871894");;

(* use unit_cs as a default terminal object *)

let unit_cs = terminal_std_tri_OMKYNLT_3336871894;;

let terminal_cs = [
 terminal_hex;
 terminal_pent; 
 terminal_adhoc_quad_9563139965A; 
 terminal_adhoc_quad_9563139965B; 
 terminal_adhoc_quad_4680581274; 
 terminal_adhoc_quad_7697147739; 
 terminal_tri_3456082115; 
 terminal_tri_7720405539; 
 terminal_tri_2739661360; 
 terminal_tri_9269152105; 
 terminal_tri_4922521904; 
 terminal_quad_1637868761; 
 terminal_ear_3603097872; 
 ear_jnull; 
 terminal_tri_5405130650; 
 terminal_tri_5766053833; 
 terminal_tri_5026777310; 
 terminal_tri_7881254908; 
 terminal_std_tri_OMKYNLT_2_1 ; (* 1107929058 *)
 terminal_std_tri_7645170609; 
 terminal_std_tri_OMKYNLT_1_2 ; (* 1532755966 *)
 terminal_std_tri_7097350062; 
 terminal_std_tri_2900061606; 
 terminal_std_tri_2200527225; 
 terminal_std_tri_3106201101; 
 terminal_std_tri_9816718044; 
 terminal_std_tri_1080462150; 
 terminal_std_tri_4143829594;
 terminal_std_tri_7459553847;
 terminal_std_tri_4528012043;
 terminal_std_tri_OMKYNLT_3336871894; 
];;

forall ( is_aug_cs) terminal_cs;;
forall ( attr_free) terminal_cs;;

let is_ear cs = 
  reset_iso_cs cs  ear_cs;;


(*
****************************************
TRANSFORMATIONS
****************************************
*)

(* transfer move an M-field to a larger 
   B-fields resetting M-fields. b5 not used *)

let transfer_to = 
  let b1 cs cs' = (cs.k_cs =  cs'.k_cs) in
  let b2 cs cs' = (cs.d_cs <= cs'.d_cs) in
  let c3 cs cs' (i,j) = 
    cs.am_cs i j >= cs'.a_cs i j  && cs.bm_cs i j <= cs'.b_cs i j  in
  let b3 cs cs' = forall (c3 cs cs') (ks_cart cs) in 
  let b4 cs cs' = 
    if is_ear cs then is_ear cs'
    else subset cs'.js_cs cs.js_cs in
  let b5 cs cs' = 
    subset cs'.lo_cs cs.lo_cs && subset cs'.hi_cs cs.hi_cs &&
      subset cs'.str_cs cs.str_cs in
    fun cs cs' -> 
      attr_free cs' && 
      b1 cs cs' && b2 cs cs' && b3 cs cs' && b4 cs cs' ;;

let proper_transfer_cs cs cs' = 
  Lib.exists (fun i -> transfer_to (rotatek_cs i cs) cs') (ks_cs cs);;

let equi_transfer_cs cs cs' = 
  (cs.k_cs = cs'.k_cs) && 
 (  proper_transfer_cs cs cs' or proper_transfer_cs (opposite_cs cs) cs');;

let rec transfer_union a b = 
  match a with
      [] -> b
    | a::aas -> if exists (equi_transfer_cs a) b 
      then transfer_union aas b
      else 
	let b' = filter (not o (C equi_transfer_cs a)) b in
	  transfer_union aas (a::b');;


(* restrict shrinks to B-field down to the M-field,
   leaving M-field intact. *)


let restrict_cs cs =
    modify_cs cs ~a:cs.am_cs ~b:cs.bm_cs ();;

(* slice works on B-fields, resetting M-fields. 
   This version does not create an ear. 
   It does just one side. *)

let slice_aux cs p q dv = 
  let k = cs.k_cs in
  let p = p mod k in
  let q = q mod k in
  let q' = if (q<p) then q+k else q in
  let k' = 1+q'-p in
  let av = cs.am_cs p q in
  let bv = cs.bm_cs p q in
  let a = override cs.a_cs (p,q,av) in
  let b = override cs.b_cs (p,q,bv) in
  let _ = (k' >2) or failwith "slice_dcs underflow" in
  let _ = (k'  <  k) or failwith "slice_dcs overflow" in
  let r i = (i + k - p) mod k in
  let s i' = (i' + p) mod k in
  let shift f i' j' = f (s i') (s j') in
  let cd1 = mk_cs (k',dv,shift a, shift b,"slice") in
  let js = map (fun (i,j) -> (r i,r j)) (intersect (cart2 (p--q)) cs.js_cs) in
    modify_cs cd1 ~js:js ();;

(* calculate the value of the new d from the old one,
   using standard assumptions about the desired terminal inequalities.
   This does cases where no "ear" is involved.
   This inequality is to be used when every edge has bounds in
   one of the three intervals [2,2h0], [2h0,sqrt8], [sqrt8,3.01] *)

let slice_dstd_aux cs p q = 
  let k = cs.k_cs in
  let p = p mod k in
  let q = q mod k in
  let d = cs.d_cs in
  let q' = if (q<p) then q+k else q in
  let k' = 1+q'-p in
  let _ = (k'=3) or raise Not_found in
  let av = cs.am_cs p q in
  let bv = cs.bm_cs p q in
  let a = override cs.a_cs (p,q,av) in
  let b = override cs.b_cs (p,q,bv) in
  let edge1(i,j) = (two <= a i j  && b i j <= twoh0) in
  let edge2(i,j) = (twoh0 <= a i j && b i j <= sqrt8) && (not (edge1 (i,j))) in
  let edge3(i,j) = (sqrt8 <= a i j && b i j <= cstab) && (not (edge2 (i,j))) in
  let edge (i, j) = edge1 (i ,j) or edge2 (i, j) or edge3 (i, j) in
  let (p1,p2,p3) = (p,inc cs p,funpow 2 (inc cs) p) in
  let triedge = [(p1,p2);(p2,p3);(p3,p1)] in
  let _ = forall edge triedge or failwith "slice_dstd" in 
  let c_edge1 = length (filter (edge1) triedge) in
  let c_edge2 = length (filter (edge2) triedge) in
  let c_edge3= length (filter (edge3) triedge) in
  let eps = tame_table_d 2 1 -. 0.11 in 
  let d12 = tame_table_d 1 2 in
  let m3 = eps *. float_of_int (c_edge3) in
  let flat1 = (c_edge1=2) && (c_edge2=1), tame_table_d 2 1 in
  let flat2 = (c_edge1=2) && (c_edge3=1), 0.11 in
  let atype = (c_edge1=1) && (c_edge2+c_edge3 =2), d12 +.  m3 in 
  let btype = (c_edge1=0) && (c_edge2+c_edge3=3), tame_table_d 0 3 +. m3 in
  let (_,dpq) = find (fst) [flat1;flat2;atype;btype] in
    (dpq, d-. dpq);;

     
let slice_dstd cs p q = 
  let k = cs.k_cs in
  let inc3 = funpow 3 (inc cs) in
    if (k=6) && (inc3 p = q) 
    then 
      let d = cs.d_cs /. two in (d,d)
    else
      let d = 
	try slice_dstd_aux cs p q 
	with Not_found -> 
	  let (d2,d1) = slice_dstd_aux cs q p in
	    (d1,d2) in
	d;;  

let slice_cs cs p q dvpq dvqp mk_ear = 
  let _ = dvpq +. dvqp >= cs.d_cs or failwith "slice_cs:bad d" in
  let cpq = slice_aux cs p q dvpq in
  let cqp = slice_aux cs q p dvqp in
  let addj cs = modify_cs cs ~js:((0,(cs.k_cs - 1))::cs.js_cs) () in
  let cpq = if (mk_ear) then addj cpq else cpq in
  let cqp = if (mk_ear) then addj cqp else cqp in
  let _ = not(mk_ear) or is_ear cpq or is_ear cqp or failwith "slice_cs:ear" in
    [cpq;cqp];;

let slice_std cs p q =
  let (dvpq,dvqp) = slice_dstd cs p q in
  let mk_ear = false in
    slice_cs cs p q dvpq dvqp mk_ear;;

(*
let equi_transfer_cs  = 
  let f cs = map (fun i -> rotatek_cs i cs) (ks_cs cs) in
    fun cs ->
      let cases = f cs @ f (opposite_cs cs) in
	fun cs' -> (cs.k_cs = cs'.k_cs) && exists (C transfer_to cs') cases;;
*)

(* deformatin acts on M-fields, keeping the domain fixed. *)

let deform_ODXLSTC_cs p cs = 
  let p0 = dec cs p in
  let p1 = p in
  let p2 = inc cs p in
  let ks = ks_cs cs in
  let ksp = subtract ks [p] in
  let diag = subtract ks [p0;p1;p2] in
  let _ = mem p ks or failwith "odx:out of range" in
  let _ = not(memj cs (p0,p1)) or raise Unchanged in
  let _ = not(memj cs (p1,p2)) or raise Unchanged in
  let _ = not(mem p cs.lo_cs) or raise Unchanged in
  let m q =  (cs.a_cs p1 q = cs.bm_cs p1 q) in
  let _ = forall (not o m) ksp or raise Unchanged in
  let n q = (fourh0 < cs.b_cs p1 q) in
  let _ = forall n diag or raise Unchanged in
  let cs1 = modify_cs cs ~lo:(sortuniq (p::cs.lo_cs)) () in
  let csp q = 
    if (cs.am_cs p q > cs.a_cs p q) then None
    else Some (modify_cs cs ~bm:(override cs.bm_cs (p,q,cs.a_cs p q)) ()) in 
    cs1::(filter_some(map csp ksp));;

let deform_IMJXPHR_cs p cs = 
  let p0 = dec cs p in
  let p1 = p in
  let p2 = inc cs p in
  let ks = ks_cs cs in
  let ksp = subtract ks [p] in
  let diag = subtract ks [p0;p1;p2] in
  let _ = mem p ks or failwith ("imj:out of range"^(string_of_int p)) in
  let _ = mem p cs.str_cs or raise Unchanged in 
  let _ = not(memj cs (p0,p1)) or raise Unchanged in
  let _ = not(memj cs (p1,p2)) or raise Unchanged in
  let _ = not(mem p cs.lo_cs) or raise Unchanged in
  let m q =  (cs.a_cs p1 q = cs.bm_cs p1 q) in
  let _ = forall (not o m) diag or raise Unchanged in
  let _ = (m p0 <> m p2) or raise Unchanged in  (* boolean xor *)
  let p' = if (m p0) then p0 else p2 in
  let ksp' = subtract ksp [p'] in
  let n q = (fourh0 < cs.b_cs p1 q) in
  let _ = forall n diag or raise Unchanged in
  let cs1 = modify_cs cs ~lo:(sortuniq (p::cs.lo_cs)) () in
  let csp q =
    if (cs.am_cs p q > cs.a_cs p q) then None
    else Some(modify_cs cs ~bm:(override cs.bm_cs (p,q,cs.a_cs p q)) ()) in 
    cs1::(filter_some(map csp ksp'));;

let deform_NUXCOEA_cs p cs =     
  let p0 = dec cs p in
  let p1 = p in
  let p2 = inc cs p in
  let ks = ks_cs cs in
  let ksp = subtract ks [p] in
  let diag = subtract ks [p0;p1;p2] in
  let _ = mem p ks or failwith ("nux:out of range"^(string_of_int p)) in
  let _ = mem p cs.str_cs or raise Unchanged in 
  let _ = not(memj cs (p0,p1)) or raise Unchanged in
  let _ = not(memj cs (p1,p2)) or raise Unchanged in
  let m q =  (cs.a_cs p1 q = cs.bm_cs p1 q) in
  let _ = forall (not o m) diag or raise Unchanged in
  let _ = (m p0 <> m p2) or raise Unchanged in  (* boolean xor *)
  let p' = if (m p0) then p0 else p2 in
  let ksp' = subtract ksp [p'] in
  let n q = (fourh0 < cs.b_cs p1 q) in
  let _ = forall n diag or raise Unchanged in
  let csp q =
    if (cs.am_cs p q > cs.a_cs p q) then None
    else Some(modify_cs cs ~bm:(override cs.bm_cs (p,q,cs.a_cs p q)) ()) in 
    (filter_some(map csp ksp'));;

(* 
apply M-field deformation at (p,p+1)=(p1,p2) 
This assumes not lunar.
*)

let deform_2065952723_A1_single p cs =
  let p1 = p in
  let p2 = inc cs p in
  let ks = ks_cs cs in
  let alldiag' = alldiag cs in 
  let _ = mem p ks or failwith "206:out of range" in
  let _ = (arc 2. 2. (cs.b_cs p1 p2) < arc 2. 2. (sqrt(15.53))) or
    raise Unchanged in
  let _ = not(memj cs (p1,p2)) or raise Unchanged in
  let _ = not(mem p1 cs.str_cs) or raise Unchanged in
  let _ = not(mem p2 cs.str_cs) or raise Unchanged in
  let m (i,j) =  (cs.a_cs i j = cs.bm_cs i j) in
  let _ = forall (not o m) alldiag' or raise Unchanged in
  let _ = not (m (p1,p2)) or raise Unchanged in
  let m' (i,j) = (cs.b_cs i j = cs.am_cs i j) in
  let _ = not (m'(p1,p2)) or raise Unchanged in
  let n (i,j) = (fourh0 < cs.b_cs i j) in
  let _ = forall n alldiag' or raise Unchanged in
  let cs1 = modify_cs cs ~str:(sortuniq (p1::cs.str_cs)) () in
  let cs2 = modify_cs cs ~str:(sortuniq (p2::cs.str_cs)) () in
  let cspq (p,q) = 
    if (cs.am_cs p q > cs.a_cs p q) then None
    else Some (modify_cs cs ~bm:(override cs.bm_cs (p,q,cs.a_cs p q)) ()) in 
  let cspq' (p,q) = 
    if (cs.bm_cs p q < cs.b_cs p q) then None
    else Some (modify_cs cs ~am:(override cs.am_cs (p,q,cs.b_cs p q)) ()) in 
    cs1::cs2::
      (filter_some(cspq' (p1,p2) :: (cspq (p1,p2)) ::(map cspq alldiag')));;

(* 
apply M-field deformation at straight p=p1, double edge (p0,p1) (p1,p2) 
This assumes not lunar.
*)

let deform_2065952723_A1_double p cs =
  let p0 = dec cs p in
  let p1 = p in
  let p2 = inc cs p in
  let ks = ks_cs cs in
  let alldiag = alldiag cs in
  let _ = mem p ks or failwith "206-double:out of range" in
  let _ = (arc 2. 2. (cs.b_cs p1 p2) +. arc 2. 2. (cs.b_cs p0 p1) 
	   < arc 2. 2. (sqrt(15.53))) or
    raise Unchanged in
  let _ = not(memj cs (p1,p2)) or raise Unchanged in
  let _ = not(memj cs (p0,p1)) or raise Unchanged in
  let _ = not(mem p0 cs.str_cs) or raise Unchanged in
  let _ = mem p1 cs.str_cs or raise Unchanged in
  let _ = not(mem p2 cs.str_cs) or raise Unchanged in
  let m (i,j) =  (cs.a_cs i j = cs.bm_cs i j) in
  let _ = forall (not o m) alldiag or raise Unchanged in
  let _ = not (m (p1,p2) && m(p0,p1)) or raise Unchanged in
  let m' (i,j) = (cs.b_cs i j = cs.am_cs i j) in
  let _ = not (m'(p1,p2) && m'(p0,p1)) or raise Unchanged in
  let n (i,j) = (fourh0 < cs.b_cs i j) in
  let _ = forall n alldiag or raise Unchanged in
  let cs1 = modify_cs cs ~str:(sortuniq (p0::cs.str_cs)) () in
  let cs2 = modify_cs cs ~str:(sortuniq (p2::cs.str_cs)) () in
  let cspq (p,q) = 
    if (cs.am_cs p q > cs.a_cs p q) then None
    else Some (modify_cs cs ~bm:(override cs.bm_cs (p,q,cs.a_cs p q)) ()) in 
  let csmin =
    if (cs.am_cs p1 p2 > cs.a_cs p1 p2 or cs.am_cs p0 p1 > cs.a_cs p0 p1)
    then None
    else Some (modify_cs cs ~bm:(overrides cs.bm_cs 
      [(p0,p1),cs.a_cs p0 p1; (p1,p2),cs.a_cs p1 p2]) ()) in
  let csmax = 
    if (cs.bm_cs p1 p2 < cs.b_cs p1 p2 or cs.bm_cs p0 p1 < cs.b_cs p0 p1) 
    then None
    else Some (modify_cs cs ~am:(overrides cs.am_cs 
      [(p0,p1),cs.b_cs p0 p1; (p1,p2),cs.b_cs p1 p2]) ()) in
    cs1::cs2::(filter_some(csmin :: csmax:: (map cspq alldiag)));;


(* 
apply M-field deformation at (p,p+1)=(p1,p2) 
*)

(*
correction -- originally I had constraints on the straightness
of p0. By the beta lemma for nonreflexive local fans, the
azimuth angle is decreasing at p0 as p1 pivots in the direction of p2.
So cs0 is not used.
*)

let deform_4828966562 p0 p1 p2 cs =
  let ks = ks_cs cs in
  let diag = subtract ks [p0;p1;p2] in
  let _ = mem p1 ks or failwith "482:out of range" in
  let _ = (three <= cs.a_cs p0 p2) or     raise Unchanged in
  let _ = (cs.b_cs p1 p2 <= twoh0) or raise Unchanged in
  let _ = (cs.b_cs p0 p1 <= cstab) or raise Unchanged in
  let _ = (cs.a_cs p1 p2 < cs.bm_cs p1 p2) or raise Unchanged in
  let _ = not(memj cs (p1,p2)) or raise Unchanged in
(*  let _ = not(mem p0 cs.str_cs) or raise Unchanged in *)
  let _ = not(mem p1 cs.str_cs) or raise Unchanged in
  let _ = not(mem p2 cs.str_cs) or raise Unchanged in
  let m q =  (cs.a_cs p1 q = cs.bm_cs p1 q) in
  let _ = forall (not o m) diag or raise Unchanged in
  let n q = (fourh0 < cs.b_cs p1 q) in
  let _ = forall n diag or raise Unchanged in
  let cs0 = modify_cs cs ~str:(sortuniq (p0::cs.str_cs)) () in 
  let cs1 = modify_cs cs ~str:(sortuniq (p1::cs.str_cs)) () in
  let cs2 = modify_cs cs ~str:(sortuniq (p2::cs.str_cs)) () in
  let cspq q = 
    if (cs.am_cs p1 q > cs.a_cs p1 q) then None
    else Some (modify_cs cs ~bm:(override cs.bm_cs (p1,q,cs.a_cs p1 q)) ()) in 
    (* cs0:: *)  cs1::cs2::
      (filter_some( (cspq p2) ::(map cspq diag)));;

let deform_4828966562A p cs =
  let p0 = dec cs p in
  let p1 = p in
  let p2 = inc cs p in
  deform_4828966562 p0 p1 p2 cs;;

let deform_4828966562B p cs =
  let p0 = dec cs p in
  let p1 = p in
  let p2 = inc cs p in
  deform_4828966562 p2 p1 p0 cs;;

(*
Obsolete comment.
Use obtuse angle at p1 to avoid node straigtenings.
Uses "1117202051" and "4559601669" for obtuseness criteria.
//This one could cause infinite looping because we are deleting
//attributes str_cs at p0 p1.
Only use as a last resort.

Update: looping prevented.
Deformation is a bad word to be using, we are not actually
deforming, we are listing the constraints that prevent deformation.
The deformation might be a diagonal at its lower bound,
a straight node at p1, or an edge (p1,p2) at its lower bound.

If there are other conditions in the aug. constraint system, that is ok.
If mem p2 cs.str_cs, then we don't need to eliminate it, because
we never deform it.  We are just saying that if an element of M_s
has a straight node at p2, then it must also have some other constraint
that prevents deformation.

So I have modified the code so not to remove p0 p2 from str_cs.

*)

(*
new condition for obtuseness by spherical law of cosines.
if p3 p4 are both straight, then the three segments
give cos(3.0 *. arc 2.52 2.52 2.) < -0.76 < -0.6.
If there are a total of 3 straights, then we have an effective triangle.
assume p1 p2 are not straight and the side p1 p2 [2,2.52].
Then (0.206,0.685)=(cos(arc 2. 2. 2.52),cos(arc 2.52 2.52 2.)).
By the sloc, cos c - cos a cos b <= cos c + |cos a cos b|
  < cos c + 0.6 < 0. and we are obtuse.
p3 is straight if it is an effective triangle p1,p2 not str, p0 p4 str.
*)


let deform_4828966562_obtuse p0 p1 p2 cs =
  let ks = ks_cs cs in
  let diag = subtract ks [p0;p1;p2] in
  let _ = mem p1 ks or failwith "482:out of range" in
  let _ = (cstab <= cs.a_cs p0 p2) or     raise Unchanged in
  let _ = (cs.b_cs p1 p2 <= twoh0) or raise Unchanged in
  let _ = (cs.b_cs p0 p1 <= twoh0) or raise Unchanged in
  let obtuse_crit = 
    ((cs.bm_cs p0 p1= two) && (mem p2 cs.lo_cs)) or
      (mem p0 cs.lo_cs && mem p2 cs.lo_cs) or 
      ((cs.bm_cs p0 p1=two) && (mem p0 cs.lo_cs) ) in
  let p4 = funpow 3 (inc cs) p1 in
  let obtuse_sloc = 
    (cs.k_cs = 6) &&
    (length (sortuniq cs.str_cs) = 3) && (subset [p0;p4] cs.str_cs) &&
      (cs.bm_cs p1 p2 <= twoh0) && not (mem p1 cs.str_cs) &&
      not (mem p2 cs.str_cs) in
  let _ = obtuse_crit or obtuse_sloc or raise Unchanged in    
  let _ = (cs.a_cs p1 p2 < cs.bm_cs p1 p2) or raise Unchanged in
  let _ = not(memj cs (p1,p2)) or raise Unchanged in
  let _ = not(mem p1 cs.str_cs) or raise Unchanged in
  let m q =  (cs.a_cs p1 q = cs.bm_cs p1 q) in
  let _ = forall (not o m) diag or raise Unchanged in
  let n q = (fourh0 < cs.b_cs p1 q) in
  let _ = forall n diag or raise Unchanged in
  let cs' = cs in (*modify_cs cs ~str:(subtract cs.str_cs [p0;p2]) () in *)
  let cs1 = modify_cs cs' ~str:(sortuniq (p1::cs'.str_cs)) () in
  let cspq q = 
    if (cs.am_cs p1 q > cs.a_cs p1 q) then None
    else Some (modify_cs cs' ~bm:(override cs.bm_cs (p1,q,cs.a_cs p1 q)) ()) in 
    cs1:: filter_some (map cspq (p2::diag));;

let deform_4828966562A_obtuse p cs =
  let p0 = dec cs p in
  let p1 = p in
  let p2 = inc cs p in
  deform_4828966562_obtuse p0 p1 p2 cs;;

let deform_4828966562B_obtuse p cs =
  let p0 = dec cs p in
  let p1 = p in
  let p2 = inc cs p in
  deform_4828966562_obtuse p2 p1 p0 cs;;

(*

range calculations for 6843920790.
2.0 *. arc 2.52 2.52 2.0 > arc 2.0 2.0 2.38;;
2.0 *. arc 2.0 2.0 2.52 < arc 2.0 2.0 (sqrt(15.53));;
As the documentation for this inequality indicates, it is
applied to the triangle p4 p1 p2.
*)


let deform_6843920790 p1 cs =
  let _ = (cs.k_cs = 5) or raise Unchanged in
  let ks = ks_cs cs in
  let p0 = dec cs p1  in
  let p2 = inc cs p1  in
  let p3 = inc cs p2  in
  let p4 = inc cs p3  in
  let diag = subtract ks [p0;p1;p2] in
  let _ = mem p1 ks or failwith "684:out of range" in
  let _ = (cs.am_cs p1 p2 = cstab && cstab = cs.bm_cs p1 p2)
    or raise Unchanged in
  let _ = (cstab <= cs.am_cs p1 p4) or raise Unchanged in
  let _ = (cstab <= cs.am_cs p4 p2) or raise Unchanged in
  let f (i,j) = (cs.bm_cs i j <= twoh0) in
  let _ = forall f [(p0,p1);(p2,p3);(p3,p4);(p4,p0)] or raise Unchanged in
  let _ = (cs.a_cs p1 p2 < cs.bm_cs p1 p2) or raise Unchanged in
  let _ = not(memj cs (p1,p2)) or raise Unchanged in
  let _ = not(mem p1 cs.str_cs) or raise Unchanged in
  let _ = not(mem p2 cs.str_cs) or raise Unchanged in
  let m q =  (cs.a_cs p1 q = cs.bm_cs p1 q) in
  let _ = forall (not o m) diag or raise Unchanged in
  let n q = (fourh0 < cs.b_cs p1 q) in
  let _ = forall n diag or raise Unchanged in
  let cs1 = modify_cs cs ~str:(sortuniq (p1::cs.str_cs)) () in
  let cs2 = modify_cs cs ~str:(sortuniq (p2::cs.str_cs)) () in
  let cspq q = 
    if (cs.am_cs p1 q > cs.a_cs p1 q) then None
    else Some (modify_cs cs ~bm:(override cs.bm_cs (p1,q,cs.a_cs p1 q)) ()) in 
     cs1::cs2::
      (filter_some( (cspq p2) ::(map cspq diag)));;


(*
****************************************
 subdivison
****************************************
*)

(* division acts on B-fields, shrinks domain.
   The global minima Ms remain global minima on smaller domain.
   We can keep attributes.
   Avoid Unchanged.  Pass through if c is out of range. 
   Restricts the domain if possible. *)

let subdivide_cs p q c cs =
  let _ = (0 <= p && p< cs.k_cs) or failwith "p out of range divide_cs" in
  let _ = (0 <= q && q< cs.k_cs) or failwith "q out of range divide_cs" in
  let (p,q) = psort(p,q) in
  let a = cs.a_cs p q in
  let b = cs.b_cs p q in
  let am = cs.am_cs p q in
  let bm = cs.bm_cs p q in
(*  let _ =  (a < c  && c < b) or raise Unchanged in *)
  let cs1 = modify_cs cs ~b:(override cs.b_cs (p,q,c)) () in
  let cs2 = modify_cs cs ~a:(override cs.a_cs (p,q,c)) () in
    if not (a < c && c < b) then [cs]
    else if bm <= c then [cs1]
    else if c <= am then [cs2]
    else (* am < c < bm *)
      let cs1' = modify_cs cs1 ~bm:(override cs.bm_cs (p,q,c)) () in
      let cs2' = modify_cs cs2 ~am:(override cs.am_cs (p,q,c)) () in
	[cs1';cs2'];;

let between_cs c cs (i,j) = 
  (cs.a_cs i j < c && c < cs.b_cs i j );;

let can_subdivide c cs =
  exists (between_cs c cs) (alldiag cs);;

let find_subdivide_edge c cs =
  let diag = alldiag cs in
  let ind = index true (map (between_cs c cs) diag) in
    List.nth diag ind;;

let subdivide_c_diag c = 
  let p = partition (can_subdivide c) in
  let rec sub init term =
    match init with
      | [] -> term 
      | cs::css -> 
	    let (i,j) = find_subdivide_edge c cs in
	    let kss = subdivide_cs i j c cs in
	    let (u,v) = p kss in
	      sub (u @ css) (v @ term) in
    fun init ->
      let (u,v) = p init in
	sub u v;;


(* claim arrows serve as documentation for
   how the calculations are progressing from initial cs to terminal cs.
*)
(* a = what we assert to prove at that point, 
   b=what we leave for later *)

let remaining = ref [];;
remaining := init_cs;;

(*
let claim_arrow (a,b) = 
  let et = map equi_transfer_cs a in
  let p cs = exists (fun f -> f cs) et in
  let _ = remaining := (filter (not o p) !remaining) in
  let tt = map equi_transfer_cs terminal_cs in
  let q cs = exists (fun f -> f cs) tt in
  let b' = filter (not o q) b in
  let _ = remaining := b' @ !remaining in
    !remaining;;
*)

let claim_arrow(a,b) = 
  let r = !remaining in
  let transfers_to_a cs = exists (equi_transfer_cs cs) a in
  let r' = filter (not o transfers_to_a) r in
  let transfers_from_b cs = exists (C equi_transfer_cs cs) b in
  let r'' = filter (not o transfers_from_b) r' in
  let _ = remaining := (b @ r'') in
    !remaining;;

  (* reduce remaining if r transfers to a.
     remove from b those that transfer to terminal.
     put residual b back in remaining.
  *)

(*
****************************************
HEXAGONS
****************************************
*)

(* flow on hexagons.
  hex-std-
   subdivide all diags at stab.
   apply deformations,
     in cyclic repetition.
      setting aside all cs st ?bm diag <= stab.
   checking they are is_aug_cs.
      
*)

(* claim  in this section goes as follows *)

hex_std_cs;;

let hex_std_preslice_02,hex_std_preslice_03 = 
  let c1 = subdivide_cs 0 2 cstab hex_std_cs in
  let c2 = subdivide_cs 0 3 cstab hex_std_cs in
    hist (hd c1) "hex_std_preslice 02" , hist (hd c2) "hex_std_preslice 03";;

claim_arrow([hex_std_cs],[hex_std_preslice_02;hex_std_preslice_03]);;

(* end claim *)


let ok_for_more_hex cs = 
  let _ = 
    try is_aug_cs cs 
    with Failure s -> report_cs cs; failwith s in
  let bstr = 3 + length (cs.str_cs) <= cs.k_cs in
  let generic_at i = 
    let p0 = i in
    let p1 = inc cs i in
    let p2 = inc cs p1 in
    let p3 = inc cs p2 in
      not (subset[p0;p1;p2;p3] cs.lo_cs && subset[p1;p2] cs.str_cs) in
  let bg = forall generic_at (ks_cs cs) in
  let bunfinished = not (transfer_to cs terminal_hex) in
    bstr && bg && bunfinished;;

let deformations bf k = 
  let r f p cs = filter bf (f p cs) in
  let m d = map (r d) (0--(k-1)) in
  let u =   [deform_ODXLSTC_cs;
	     deform_IMJXPHR_cs;
	     deform_NUXCOEA_cs;
	     deform_4828966562A_obtuse;
	     deform_4828966562B_obtuse;
	     deform_2065952723_A1_single;
	     deform_2065952723_A1_double;
	     deform_4828966562A;
	     deform_4828966562B;
	    deform_6843920790] in
    List.flatten (map m u);;

let hex_deformations = deformations ok_for_more_hex 6;;

let name_of k i =
  let names_hex = 
    ["odx";"imj";"nux";"482ao";"482bo";"206s";"206d";"482a";"482b";"684"] in
  let offset = i mod k in
  let s = i/k in
    (List.nth names_hex s) ^ "-" ^ (string_of_int offset);;

let name_of_hex = name_of 6;;

let transfer_hex_to_preslice = 
  let e02 = C equi_transfer_cs (hex_std_preslice_02) in
  let e03 = C equi_transfer_cs (hex_std_preslice_03) in
    fun cs -> e02 cs or e03 cs;;

let subdivide_without_preslice transfer init  = 
  let sub = subdivide_c_diag cstab init in
    filter (not o transfer) sub;;

let hex_subdivide_without_preslice = subdivide_without_preslice
 transfer_hex_to_preslice [hex_std_cs];;

let preslice_ready cs = 
  if (cs.k_cs=4) && (cs.d_cs=0.467) 
  then
    (cs.bm_cs 0 2 = three) && (cs.bm_cs 1 3 = three)
  else  
    exists (fun (i,j) -> cs.bm_cs i j <= cstab ) (alldiag cs);;
    
let rec general_loop df tr c active stab_diags =
    if (c <= 0) or length stab_diags > 0 then (active,stab_diags) 
    else match active with
	[] -> ([],stab_diags) 
      | (i,cs)::css -> 
	    try 
	      let kss = List.nth df i cs in
	      let (u,v) = partition preslice_ready kss in
	      let u' = filter (not o tr) u in
	      let v' = map (fun cs -> (0,cs)) v in
		general_loop df tr (c-1) (v' @ css) (u' @  stab_diags)
	    with Unchanged -> 
	      general_loop df tr (c-1) ((i+1,cs)::css) stab_diags
              | Failure s -> ( ((-1,cs)::css,stab_diags));;

let hex_loop = general_loop hex_deformations transfer_hex_to_preslice;;

let execute_hexagons() = 
    hex_loop 200000 
      (map (fun i->(0,i)) hex_subdivide_without_preslice) [];;

(* if hl = ([],[]) successful, it means that all hexagons have been reduced
   to the one terminal hexagon, together with two cases of hex_std_preslice
*)

(* execute_hexagons();; working in svn:2819 *)

(*
****************************************
PENTAGONS
****************************************
*)

(* flow on pentagons is the same as for hexagons *)

let ok_for_more_pent cs = 
  let _ = 
    try is_aug_cs cs 
    with Failure s -> report_cs cs; failwith s in
  let bstr = 3 + length (cs.str_cs) <= cs.k_cs in
  let sph_tri_ineq i = 
    let p0 = i in
    let p1 = inc cs p0 in
    let p2 = inc cs p1 in
    let p3 = inc cs p2 in
    let p4 = inc cs p3 in
      if not(subset [p1;p2] cs.str_cs) then true
      else
	let htmin = two in
	let htmax p = if mem p cs.lo_cs then two else twoh0 in
	let e03min = arc (htmax p0) (htmax p1) (cs.am_cs p0 p1) +.
	  arc (htmax p1) (htmax p2) (cs.am_cs p1 p2) +.
	  arc (htmax p2) (htmax p3) (cs.am_cs p2 p3) in
	let e03max = arc (htmin) (htmin) (cs.bm_cs p3 p4) +.
	  arc (htmin) (htmin) (cs.bm_cs p4 p0) in
	  e03min <= e03max in
  let bunfinished = not (transfer_to cs terminal_pent) in
    bstr && bunfinished && forall sph_tri_ineq (ks_cs cs);;

let pent_deformations = deformations ok_for_more_pent 5;;

let name_of_pent = name_of 5;;

let slice_hex_to_pent_tri = 
  let cs = hex_std_preslice_02 in
  let d'= 0.616 in 
  let d = cs.d_cs -. d' in 
  let vv = slice_cs cs 2 0 d' d  false in
    map (C hist "slice_hex_to_pent_tri") vv;;

exists (equi_transfer_cs pent_pro_cs) slice_hex_to_pent_tri;;

claim_arrow([pent_pro_cs;hex_std_preslice_02],slice_hex_to_pent_tri);;

let pent_init = 
  [pent_std_cs;pent_diag_cs] @ filter (fun cs -> (5=cs.k_cs)) 
    slice_hex_to_pent_tri;; 

let pent_composite_cs = mk_cs (
   5,
   0.616,
   a_pro two two cstab 5,
   a_pro cstab twoh0 upperbd 5,"pent composite");;

let pent_comp_rediag_cs (p,q) = 
  let cs = pent_composite_cs in
  modify_cs cs
    ~b:(override cs.b_cs (p,q,cstab))
	  ~bm:(override cs.bm_cs (p,q,cstab)) ();;

let pent_preslice = 
  let alld = alldiag pent_std_cs in
  let ffh ((p,q), cs) = subdivide_cs p q cstab cs in
  let preslices = List.flatten (map ffh (cart alld pent_init)) in
  let pent_comb = map pent_comp_rediag_cs alld (* [(1,4);(0,3);(4,2)] *) in
  let cstab_preslices = filter preslice_ready (pent_comb @ preslices) in
  let union_cstab_preslices = transfer_union cstab_preslices [] in 
    map (C hist "preslice") union_cstab_preslices;;

let transfer_pent_to_preslice = 
  let f1 = map (C equi_transfer_cs) pent_preslice in
    fun cs -> exists (fun f -> f cs) f1;;

let pent_subdivide_without_preslice = 
  let pl = subdivide_without_preslice 
    transfer_pent_to_preslice pent_init in
    transfer_union pl [pent_composite_cs];;

(* pent section main claim *)

claim_arrow(pent_init,pent_subdivide_without_preslice @pent_preslice);;

let pent_loop = general_loop pent_deformations transfer_pent_to_preslice;;

let execute_pentagons() = 
    pent_loop 200000 
      (map (fun i->(0,i)) pent_subdivide_without_preslice) [];;

let hl = execute_pentagons();;

(* if hl = ([],[]) successful, it means that all pentagons have been reduced
   to the one terminal pentagon, together with cases of pent_preslice
   worked in svn:2821, May 20, 2012.
*)

(*
****************************************
QUADRILATERALS
****************************************
*)

let (quad_477_preslice_short,quad_477_preslice_long) = 
  let preslices = subdivide_c_diag cstab [quad_pro_cs] in
  let vv =  (map (C hist "preslice pro") preslices) in
  let p = filter (fun cs -> cs.b_cs 0 2 = cstab) 
    (subdivide_cs 0 2 cstab quad_pro_cs) in
  let ww = transfer_union (p @ vv) [] in
    partition preslice_ready ww;;

let handle_quad_477_preslice_short = 
  let _ = (length quad_477_preslice_short = 1) or failwith "handle 477" in
  let cs = hd quad_477_preslice_short in
  let mk_ear = true in
  let inc2 = funpow 2 (inc cs) in
  let f i =  slice_cs cs i (inc2 i) (0.11) (0.477 -. 0.11) mk_ear in
  let ind = filter (can f) (0--3) in
  let g i = 
    forall (fun u -> exists (equi_transfer_cs u) terminal_cs) (f i) in
    exists g ind;;

claim_arrow([quad_pro_cs],quad_477_preslice_long);;

let terminal_quad = 
  quad_477_preslice_short @ terminal_cs;;

let ok_for_more_tri_quad cs = 
  let _ = (cs.k_cs <=4  && cs.k_cs >= 3) or failwith "tri quads only" in
  let b467_2485876245a = 
    if (cs.d_cs=0.467) && (cs.k_cs = 4) &&
      forall (fun (i,j)-> cs.bm_cs i j <= twoh0) [(0,1);(1,2);(2,3);(3,0)] &&
      forall (fun (i,j)-> cs.am_cs i j >= three) [(0,2);(1,3)]
    then ( cs.str_cs = []) else true in
  let b477 =
    let b477k = (cs.k_cs = 4) in
    let b477a =  cs.str_cs = [] in
    let b477b = Sphere_math.delta_y (* if neg then geometric impossibility *)
      (cs.bm_cs 0 1) (cs.bm_cs 0 3) (cs.am_cs 0 2)
      (cs.bm_cs 2 3) (cs.bm_cs 1 2) (cs.am_cs 1 3) >= 0.0 in
    let b477c = 
      not(exists (equi_transfer_cs cs) quad_477_preslice_short) in
    if (cs.d_cs=0.477) &&
      forall (fun (i,j)-> cs.bm_cs i j <= twoh0) [(0,1);(1,2);(2,3);(3,0)] &&
      forall (fun (i,j)-> cs.am_cs i j >= cstab) [(0,2);(1,3)]
    then (b477k && b477a && b477b && b477c) else true in      
  let _ = 
    try is_aug_cs cs 
    with Failure s -> report_cs cs; failwith s in
  let bstr = 3 + length (cs.str_cs) <= cs.k_cs in
  let bunfinished = not (exists (transfer_to cs) terminal_quad) in
    bstr && bunfinished && b467_2485876245a && b477 ;;

let quad_deformations = deformations ok_for_more_tri_quad 4;;

let name_of_quad = name_of 4;;

let tri_deformations = deformations ok_for_more_tri_quad 3;;

let name_of_tri = name_of 3;;

let transfer_quad_to_terminal = 
  let f1 = map (C equi_transfer_cs) terminal_quad in
    fun cs -> exists (fun f -> f cs) f1;;

let quad_loop = general_loop quad_deformations transfer_quad_to_terminal;;

let special_quad_init = 
  let special_situations cs =  
    (0.467=cs.d_cs) or (0.477=cs.d_cs) in
    filter (fun cs -> (4=cs.k_cs) && special_situations cs) (!remaining);;

let execute_special_quads() = 
    quad_loop 200000 
      (map (fun i->(0,i)) special_quad_init) [];;

let hl = execute_special_quads();;

claim_arrow(special_quad_init,[]);;

(* if hl = ([],[]) successful, it means that 
   all special quads have been reduced
   to terminal quads, 
   worked in svn:2821, May 20, 2012.
*)


(* now the general case remains
   policies and procedure:
   - no more use of js_cs and ears.
   - determine d by slice_dpq procedure.

   1- if the cs transfers to a terminal or is not "ready" for more, 
   then were are done with it.
   2- if stab is between lower and upper bounds of a diag, then subdivide it
   3- if sqrt8 is between lower and upper bounds of a diag, then 
   4- if there is a diag [2h0,sqrt8], then slice it.
   5- if there is a diag [sqrt8,cstab], then slice it.
   6- if a deformation applies, then apply it.
   7- do "upper echelon" treatment of quads (subdivisions on edges > 3.01)

*)

XXD;;

let handle_general_case cs = 
  (* 1- *)
  if (cs.k_cs = 6) && not(ok_for_more_hex cs) then []
  else if (cs.k_cs=5) && not(ok_for_more_pent cs) then []
  else if not(ok_for_more_tri_quad cs) then []
  else if exists (equi_transfer_cs cs) terminal_quad then []
    (* 2- *)
  else if (can_subdivide cstab cs) then (subdivide_c_diag cstab [cs])
    (* 3- *)
  else if (can_subdivide sqrt8 cs) then (subdivide_c_diag sqrt8 [cs])
    (* 4- *)
  else [];;
    

(* XXD to here.
let squiggle1 cs = 
  if not (ok_for_more_tri_quad cs) then []
  else if 
*)







(*
let slice_hex_to_quad = 
  let cs = hex_std_preslice_03 in
  let d = cs.d_cs /. 2.0 in 
  let vv = slice_cs cs 3 0 d d  false in
    transfer_union (map (C hist "slice_hex_to_quad") vv) [];;


claim_arrow([hex_std_preslice_03],slice_hex_to_quad);;
*)







(* temporary *)










(*
let quad_subdivide_without_preslice = 
  let pl = subdivide_without_preslice 
    transfer_quad_to_preslice quad_init in
    transfer_union pl [quad_composite_cs];;
*)



!remaining;;

(* scratch area *)

length ( (fst hl));;
report (string_of_cs (snd(hd (fst hl))));;
nth hex_deformations 3;;
is_cs (!csbad);;
let cs1 = (snd(hd (fst hl)));;
let cs1 = ((hd (snd hl)));;
report_cs cs1;;
ok_for_more_pent cs1;;

let cs1 = !csbad;;

let fg cs r = 
  try List.nth hex_deformations r cs; true
  with Unchanged -> false;;
filter (fg cs1) (0--53);;
map name_of_hex it;;


let fr r = List.nth hex_deformations r cs1;;
fr 0;;
let pp = partition preslice_ready it;;
map report_cs (snd pp);;
name_of_hex 52;;
let cs2 = it;;
report_cs (hd(snd cs2));;


52 / 5;;
let cs1 = !csbad;;
List.length hex_deformations;;
deform_4828966562_obtuse 2 3 4 cs1;;

deform_NUXCOEA_cs 0 cs1;;
map report_cs it;;
partition preslice_ready it;;
let cs2 = hd (snd(it));;
report_cs cs2;;


let subdivide_without_preslice transfer init  = 
  let sub = subdivide_c_diag cstab init in
    filter (not o transfer) sub;;

(* XXD broken *)

let hex_subdivide_without_preslice = subdivide_without_preslice
 transfer_hex_to_preslice [hex_std_cs];;

let hh= subdivide_c_diag cstab [hex_std_cs];;
length hh;;
let h2 = filter preslice_ready hh;;
length h2;;
let cs = hd h2;;
report_cs cs;;
transfer_hex_to_preslice cs;;

let transfer_hex_to_preslice = 
  let e02 = equi_transfer_cs (hex_std_preslice_02) in
  let e03 = equi_transfer_cs (hex_std_preslice_03) in
    fun cs -> e02 cs or e03 cs;;

equi_transfer_cs cs hex_std_preslice_02;;

!remaining;;




(* deal with pent_diag *)

let preslice_pent_diag = 
  let css = hd (filter (fun cs -> mem"pent diag init" cs.history_cs) 
		  !remaining) in
    css;;

let slice_pd_to_quad = 
  let cs = preslice_pent_diag in
  let vv = slice_cs cs 0 2 (0.11) (cs.d_cs -. 0.11) false in
  let vv' = filter (fun v -> not ( exists (equi_transfer_cs v) terminal_cs)) vv in 
    (map (C hist "slice pent to quad") vv');;

claim_arrow ([preslice_pent_diag],slice_pd_to_quad);;

report_cs slice_pent_diag;;
equi_transfer_cs;;


let (quad_pd_short,quad_pd_long) = 
  let preslices = subdivide_c_diag cstab [quad_pro_cs] in
  let vv =  (map (C hist "preslice pro") preslices) in
  let p = filter (fun cs -> cs.b_cs 0 2 = cstab) 
    (subdivide_cs 0 2 cstab quad_pro_cs) in
  let ww = transfer_union (p @ vv) [] in
    partition preslice_ready ww;;
