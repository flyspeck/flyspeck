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


let mk_j cs i = psort (i,inc cs i);;

let ink k i = (i+1) mod k;;

let dek k i = (i+k-1) mod k;;

let inc cs i = ink cs.k_cs i;;

let dec cs i = dek cs.k_cs i;;

let inka k a = 
    map (ink k) a;;

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

let map_cs f cs = 
  let a' a i j = a (f i) (f j) in
  let f2 (i,j) = psort (f i , f j ) in
  {
    k_cs = cs.k_cs;
    d_cs = cs.d_cs;
    a_cs = a' (cs.a_cs);
    b_cs = a' (cs.b_cs);
    am_cs = a' (cs.am_cs);
    bm_cs = a' (cs.bm_cs);
    lo_cs = map f cs.lo_cs;
    hi_cs = map f cs.hi_cs;
    str_cs = map f cs.str_cs;
    js_cs = map f2 cs.js_cs;
    history_cs = cs.history_cs;
  };;

let opposite_cs cs = 
  let r i = (cs.k_cs - (i+1)) in
    map_cs r cs;;

let rotate_cs cs = map_cs (inc cs) cs;;

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
  let bj = set_eq cs.js_cs cs'.js_cs in
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

let mk_cs (k,d,a,b) = {
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
  history_cs = [];
};;

let hex_std_cs = mk_cs (6, tame_table_d0 6,
  cs_adj two twoh0 6,
  cs_adj twoh0 upperbd 6);;

let pent_std_cs = mk_cs (5,tame_table_d0 5,
  cs_adj two twoh0 5,
  cs_adj twoh0 upperbd 5);;

let quad_std_cs = mk_cs (4,tame_table_d0 4,
  cs_adj two twoh0 4,
  cs_adj twoh0 upperbd 4);;

let tri_std_cs = mk_cs (3,tame_table_d0 3,
  cs_adj two twoh0 3,
  cs_adj twoh0 upperbd 3);;

let pent_diag_cs = mk_cs (
   5,
   0.616,
   cs_adj two sqrt8 5,
   cs_adj twoh0 upperbd 5);;

let quad_diag_cs = mk_cs (
   4,
   0.467,
   cs_adj two sqrt8 4,
   cs_adj twoh0 upperbd 4);;

let pent_pro_cs = mk_cs (
   5,
   0.616,
   a_pro twoh0 two twoh0 5,
   a_pro sqrt8 twoh0 upperbd 5);;

let quad_pro_cs = mk_cs (
   4,
   0.477,
   a_pro twoh0 two twoh0 4,
   a_pro sqrt8 twoh0 upperbd 4);;

let init_cs = [
  hex_std_cs;
  pent_std_cs;
  quad_std_cs;
  tri_std_cs;
  pent_diag_cs;
  quad_diag_cs;
  pent_pro_cs;
  quad_pro_cs;
];;

map is_aug_cs init_cs;;
map attr_free init_cs;;

(* now for the terminal cases done by interval computer calculation *)

let terminal_hex =
mk_cs (
   6,
   tame_table_d0 6,
   cs_adj two cstab 6,
   cs_adj two upperbd 6);;

let terminal_pent = 
mk_cs (
   5,
   0.616,
   cs_adj two cstab 5,
   cs_adj two upperbd 5);;

(* two cases for the 0.467 bound: all top edges 2 or both diags 3 *)

let terminal_adhoc_quad_9563139965A = 
mk_cs (
   4,
   0.467,
   cs_adj two three 4,
   cs_adj two upperbd 4);;

let terminal_adhoc_quad_9563139965B = 
mk_cs (
   4,
   0.467,
   cs_adj two three 4,
   cs_adj twoh0 three 4);;

let terminal_adhoc_quad_4680581274 = mk_cs(
 4,
 0.616 -. 0.11,
 funlist [(0,1),cstab ; (0,2),cstab ; (1,3),cstab ] two,
 funlist [(0,1),cstab ; (0,2),upperbd ; (1,3),upperbd ] two);;

let terminal_adhoc_quad_7697147739 = mk_cs(
 4,
 0.616 -. 0.11,
 funlist [(0,1),sqrt8 ; (0,2),cstab ; (1,3),cstab ] two,
 funlist [(0,1),sqrt8 ; (0,2),upperbd ; (1,3),upperbd ] two);;

let terminal_tri_3456082115 = mk_cs(
 3,
 0.5518 /. 2.0,
 funlist [(0,1), cstab; (0,2),twoh0; (1,2),two] two,
 funlist [(0,1), 3.22; (0,2),twoh0; (1,2),two] two);;

let terminal_tri_7720405539 = mk_cs(
 3,
 0.5518 /. 2.0 -. 0.2,
 funlist [(0,1),cstab; (0,2),twoh0; (1,2),two] two,
 funlist [(0,1),3.41; (0,2),twoh0; (1,2),two] two);;

let terminal_tri_2739661360 = mk_cs(
 3,
 0.5518 /. 2.0 +. 0.2,
 funlist [(0,1),cstab; (0,2),cstab; (1,2),two] two,
 funlist [(0,1),3.41; (0,2),cstab; (1,2),two] two);;

let terminal_tri_9269152105 = mk_cs(
 3,
 0.5518 /. 2.0 ,
 funlist [(0,1),3.41; (0,2),cstab; (1,2),two] two,
 funlist [(0,1),3.62; (0,2),cstab; (1,2),two] two);;

let terminal_tri_4922521904 = mk_cs(
 3,
 0.5518 /. 2.0 ,
 funlist [(0,1),cstab; (0,2),twoh0; (1,2),two] two,
 funlist [(0,1),3.339; (0,2),twoh0; (1,2),two] two);;

let terminal_quad_1637868761 = mk_cs(
 4,
 0.5518,
 funlist [(0,1),two; (1,2), cstab; 
                  (2,3),twoh0; (0,3),two; (0,2),3.41; (1,3),cstab] two,
 funlist [(0,1),two; (1,2), cstab;
                  (2,3),twoh0; (0,3),two; (0,2),3.634; (1,3),six] two);;


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
  history_cs= [];
};;

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
  history_cs=[];
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
  history_cs=[];
};;

let terminal_tri_5026777310 = mk_cs(
 3,
  0.6548 -. 2.0 *. 0.11,
 funlist [(0,1),sqrt8;(1,2),sqrt8] two,
 funlist [(0,1),cstab;(1,2),cstab] twoh0);;

let terminal_tri_7881254908 = mk_cs(
 3,
  0.696 -. 2.0 *. 0.11,
 funlist [(0,1),sqrt8;(1,2),sqrt8] twoh0,
 funlist [(0,1),cstab;(1,2),cstab] twoh0);;

(* 1107929058 *)
let terminal_std_tri_OMKYNLT_2_1  = mk_cs(
 3,
  tame_table_d 2 1,
 funlist [(0,1),twoh0] two,
 funlist [(0,1),twoh0] two);;

let terminal_std_tri_7645170609 = mk_cs(
 3,
  tame_table_d 2 1,
 funlist [(0,1),sqrt8] two,
 funlist [(0,1),sqrt8] two);;

(* 1532755966 *)
let terminal_std_tri_OMKYNLT_1_2  = mk_cs(
 3,
  tame_table_d 1 2,
 funlist [(0,1),two] twoh0,
 funlist [(0,1),two] twoh0);;

let terminal_std_tri_7097350062 = mk_cs(
 3,
  tame_table_d 1 2 +. (tame_table_d 2 1 -. 0.11),
 funlist [(0,1),twoh0;(0,2),sqrt8] two,
 funlist [(0,1),twoh0;(0,2),sqrt8] two);;

let terminal_std_tri_2900061606 = mk_cs(
 3,
  tame_table_d 1 2 +. (tame_table_d 2 1 -. 0.11),
 funlist [(0,1),twoh0;(0,2),cstab] two,
 funlist [(0,1),twoh0;(0,2),cstab] two);;

let terminal_std_tri_2200527225 = mk_cs(
 3,
  tame_table_d 1 2 +. 2.0*. (tame_table_d 2 1 -. 0.11),
 funlist [(0,1),two;] sqrt8,
 funlist [(0,1),two;] sqrt8);;

let terminal_std_tri_3106201101 = mk_cs(
 3,
  tame_table_d 1 2 +. 2.0*. (tame_table_d 2 1 -. 0.11),
 funlist [(0,1),two;(0,2),cstab] sqrt8,
 funlist [(0,1),two;(0,2),cstab] sqrt8);;

let terminal_std_tri_9816718044 = mk_cs(
 3,
  tame_table_d 1 2 +. 2.0*. (tame_table_d 2 1 -. 0.11),
 funlist [(0,1),two] cstab,
 funlist [(0,1),two] cstab);;

let terminal_std_tri_1080462150 = mk_cs(
 3,
  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11),
 funlist [] twoh0,
 funlist [] twoh0);;

let terminal_std_tri_4143829594 = mk_cs(
 3,
  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11),
 funlist [(0,1),cstab] twoh0,
 funlist [(0,1),cstab] twoh0);;

let terminal_std_tri_7459553847 = mk_cs(
 3,
  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11),
 funlist [(0,1),twoh0] cstab,
 funlist [(0,1),twoh0] cstab);;

let terminal_std_tri_4528012043 = mk_cs(
 3,
  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11),
 funlist [] cstab,
 funlist [] cstab);;

let terminal_std_tri_OMKYNLT_3336871894 = mk_cs(
 3,
 zero,
 funlist [] two,
 funlist [] two);;

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

map ( is_aug_cs) terminal_cs;;
map ( attr_free) terminal_cs;;

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


(* division acts on B-fields, shrinks domain.
   The global minima Ms remain global minima on smaller domain.
   We can keep attributes *)

let subdivide_cs p q c cs =
  let _ = (0 <= p && p< cs.k_cs) or failwith "p out of range divide_cs" in
  let _ = (0 <= q && q< cs.k_cs) or failwith "q out of range divide_cs" in
  let (p,q) = psort(p,q) in
  let a = cs.a_cs p q in
  let b = cs.b_cs p q in
  let am = cs.am_cs p q in
  let bm = cs.bm_cs p q in
  let _ =  (a < c  && c < b) or raise Unchanged in
  let cs1 = modify_cs cs ~b:(override cs.b_cs (p,q,c)) () in
  let cs2 = modify_cs cs ~a:(override cs.a_cs (p,q,c)) () in
    if bm < c then [cs1]
    else if c < am then [cs2]
    else (* am <= c <= bm *)
      let cs1' = modify_cs cs1 ~bm:(override cs.bm_cs (p,q,c)) () in
      let cs2' = modify_cs cs2 ~am:(override cs.am_cs (p,q,c)) () in
	[cs1';cs2'];;

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
  let cd1 = mk_cs (k',dv,shift a, shift b) in
  let js = map (fun (i,j) -> (r i,r j)) (intersect (cart2 (p--q)) cs.js_cs) in
    modify_cs cd1 ~js:js ();;

let slice_cs cs p q dvpq dvqp mk_ear = 
  let _ = dvpq +. dvqp >= cs.d_cs or failwith "slice_cs:bad d" in
  let cpq = slice_aux cs p q dvpq in
  let cqp = slice_aux cs q p dvqp in
  let addj cs = modify_cs cs ~js:((0,(cs.k_cs - 1))::cs.js_cs) () in
  let cpq = if (mk_ear) then addj cpq else cpq in
  let cqp = if (mk_ear) then addj cqp else cqp in
  let _ = not(mk_ear) or is_ear cpq or is_ear cqp or failwith "slice_cs:ear" in
    [cpq;cqp];;

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

let csbad = ref unit_cs;;

let is_ok cs = 
  let _ = 
    try is_aug_cs cs 
    with Failure s -> report_cs cs; csbad:= cs; failwith s in
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

(* flow on hexagons.
  hex-std-
   subdivide all diags at stab.
   apply deformations,
     in cyclic repetition.
      setting aside all cs st ?bm diag <= stab.

   checking they are is_aug_cs.
      
*)

let hex_deformations = 
  let r f p cs = filter is_ok (f p cs) in
  let m d = map (r d) (0--5) in
  let u =   [deform_ODXLSTC_cs;
	     deform_IMJXPHR_cs;
	     deform_NUXCOEA_cs;
	     deform_4828966562A_obtuse;
	     deform_4828966562B_obtuse;
	     deform_2065952723_A1_single;
	     deform_2065952723_A1_double;
	     deform_4828966562A;
	     deform_4828966562B;] in
    List.flatten (map m u);;

let names_def = ["odx";"imj";"nux";"482ao";"482bo";"206s";"206d";"482a";"482b";];;

let name_of_def i =
  let offset = i mod 6 in
  let s = i/6 in
    (List.nth names_def s) ^ "-" ^ (string_of_int offset);;

let has_stab_diag cs = 
    exists (fun (i,j) -> cs.bm_cs i j <= cstab ) (alldiag cs);;

let find_sub_diag cs =
  let diag = alldiag cs in
  let f (i, j) = ( cs.a_cs i j < cstab && cstab < cs.b_cs i j) in
  let ind = index true (map f diag) in
    List.nth diag ind;;

let rec split_stab_diag init term =
    match init with
      | [] -> ([],term)
      | cs::css -> 
	  try
	    let (i,j) = find_sub_diag cs in
	    let kss = subdivide_cs i j cstab cs in
	    let (u,v) = partition has_stab_diag kss in
	      split_stab_diag (v @ css) (u @ term)
	  with Failure _ -> partition (not o has_stab_diag) (cs::css @term);;

let hex_std_preslice = 
  let c1 = subdivide_cs 0 2 cstab hex_std_cs in
  let c2 = subdivide_cs 0 3 cstab hex_std_cs in
    (hd c1) , (hd c2) ;;

let transfer_hex_to_preslice cs = 
  equi_transfer_cs cs (fst hex_std_preslice) or 
    equi_transfer_cs cs (snd hex_std_preslice);;

let hex_split = 
  let (u,v) = split_stab_diag [hex_std_cs] [] in
  let _ = forall transfer_hex_to_preslice v or failwith "hex_split" in
  let u' =     map (fun i -> (0,i)) u in
    u';;
    
let rec hex_loop c active stab_diags =
    if c <= 0 then (active,stab_diags) 
    else match active with
	[] -> ([],stab_diags) 
      | (i,cs)::css -> 
	    try 
	      let kss = List.nth hex_deformations i cs in
	      let (u,v) = partition has_stab_diag kss in
	      let _ = forall transfer_hex_to_preslice v or failwith "pre" in
	      let v' = map (fun cs -> (0,cs)) v in
		hex_loop (c-1) (v' @ css) ((* u @ *) stab_diags)
	    with Unchanged -> hex_loop (c-1) ((i+1,cs)::css) stab_diags
              | Failure s -> ( ((-1,cs)::css,stab_diags));;

(* next fix failure "pre" to store failures and rerun. XXD *)

let hl = 
    hex_loop 200000 hex_split [];;

length ( (fst hl));;
report (string_of_cs (snd(hd (fst hl))));;
nth hex_deformations 3;;
is_cs (!csbad);;
let cs1 = (snd(hd (fst hl)));;
report_cs cs1;;
is_ok cs1;;

let cs1 = !csbad;;

let fg cs r = 
  try List.nth hex_deformations r cs; true
  with Unchanged -> false;;
filter (fg cs1) (0--53);;
map name_of_def it;;


let fr r = List.nth hex_deformations r cs1;;
fr 0;;
let pp = partition has_stab_diag it;;
map report_cs (snd pp);;
name_of_def 52;;
let cs2 = it;;
report_cs (hd(snd cs2));;


52 / 5;;
let cs1 = !csbad;;
List.length hex_deformations;;
deform_4828966562_obtuse 2 3 4 cs1;;

deform_NUXCOEA_cs 0 cs1;;
map report_cs it;;
partition has_stab_diag it;;
let cs2 = hd (snd(it));;
report_cs cs2;;
let fq cs (i,j) = 
 (cs.a_cs i j = cs.a_cs j i) &&
      (cs.b_cs i j = cs.b_cs j i) &&
      (cs.a_cs i j <= cs.am_cs i j) &&
      (cs.am_cs i j <= cs.bm_cs i j) &&
      (cs.bm_cs i j <= cs.b_cs i j);;

map (fun (i,j) -> (i,j,(fq cs1 (i,j)))) (ks_cart cs1);;

report_cs cs1;;
cs1.a_cs 0 5;;
cs1.b_cs 0 5;;
transfer_to cs1 terminal_hex;;

let p1 = 3;;
  
  let p2 = inc cs1 p1;;
  let ks = ks_cs cs1 ;;
  let alldiag' = alldiag cs1 ;;
  let _ = mem p1 ks or failwith "206:out of range" ;;
  let _ = (arc 2. 2. (cs1.b_cs p1 p2) < arc 2. 2. 15.53) ;;
    raise Unchanged in
  let _ = not(memj cs1 (p1,p2)) or raise Unchanged in
  let _ = not(mem p1 cs1.str_cs) or raise Unchanged in
  let _ = not(mem p2 cs1.str_cs) or raise Unchanged in
  let m (i,j) =  (cs.a_cs i j = cs.bm_cs i j) in
  let _ = forall (not o m) alldiag' or raise Unchanged in
  let _ = not (m (p1,p2)) or raise Unchanged in
  let m' (i,j) = (cs.b_cs i j = cs.am_cs i j) in
  let _ = not (m'(p1,p2)) or raise Unchanged in
  let n (i,j) = (fourh0 < cs.b_cs i j) in
  let _ = forall n alldiag' or raise Unchanged in

;;
arc 2. 2. 15.53;;
