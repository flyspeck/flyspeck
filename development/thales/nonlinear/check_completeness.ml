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

The purpose is to transform the list ur_cs into terminal_cs
in a finite sequence of regulated moves.
*)


#directory "/Users/thomashales/Desktop/googlecode/hol_light";;
#use "hol.ml";;

(*
****************************************
BASICS
****************************************
*)

let nub = Lib.uniq;;
let sortuniq xs = uniq (Lib.sort (<) xs);;

let rec cart a b = 
  match a with
    | [] -> []
    | a::rest -> (map (fun x -> (a,x)) b) @ cart rest b;;


(* a few constants *)
let zero = 0.0;;
let target = 1.541;;
let two = 2.0;;
let twoh0 = 2.52;;
let sqrt8 = Pervasives.sqrt(8.0);;
let three = 3.0;;
let cstab = 3.01;;
let six = 6.0;;  (* 6.0 > 4 * h0, upper bound on diags in BB *)

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
*)

type attrib_cs =
    Cs_straight of int
  | Cs_lo  of int
  | Cs_hi of int;;


(*
  | Cs_generic
  | Cs_lunar
  | Cs_interior_crit;; 

 Generic and lunar not closed conditions.

 Cs_hi not needed for initial reductions.

 Cs_interior_crit means all index-minimizers v 
  st. all diags are strictly between a and b. 
  Not a closed condition, don't use.
*)

let amap f a = match a with
      | Cs_straight i -> Cs_straight (f i)
      | Cs_lo i -> Cs_lo (f i)
      | Cs_hi i -> Cs_hi (f i);;

type constraint_system = 
{
  k_cs : int;
  d_cs : float;
  a_cs : int->int ->float;
  b_cs: int->int->float;
  jlist_cs : int list;
  attrib_cs : attrib_cs list;
};;

let ink k i = (i+1) mod k;;

let dek k i = (i+k-1) mod k;;

let inc cs i = ink cs.k_cs i;;

let dec cs i = dek cs.k_cs i;;

let inka k a = 
    amap (ink k) a;;

let in_j cs (i,j) = 
  ((j = inc cs i) && (mem i cs.jlist_cs)) or
   ( (i = inc cs j) &&( mem j cs.jlist_cs));;

let ks_cs cs = (0-- (cs.k_cs -1));;

let ks_cart cs = let ks = ks_cs cs in cart ks ks;;

(*
****************************************
BASIC OPS ON CONSTRAINT SYSTEMS
****************************************
*)


let is_cs cs = 
  let f (i,j) = 
    (cs.a_cs i j = cs.a_cs j i) &&
      (cs.b_cs i j = cs.b_cs j i) &&
      (cs.a_cs i j <= cs.b_cs i j) in
  let ks = ks_cs cs in
  let rl = cart ks ks in
  let bm = (uniq (map f rl) = [true]) in 
  let bs = (cs.k_cs <= 6) && (cs.k_cs >= 3) in
  let bj = List.length cs.jlist_cs + cs.k_cs <= 6 in
  let bj' = List.length (uniq cs.jlist_cs) = List.length cs.jlist_cs in
    bm && bs && bj && bj';;  


(* jlist i represents edge {i,i+1}
   reverse is {r (i+1), r i}
*)

let reverse_cs cs = 
  let r i = (cs.k_cs -(i+1)) in
  let a' a i j = a (r i) (r j) in
    {
      k_cs = cs.k_cs;
      d_cs = cs.d_cs;
      a_cs = a' (cs.a_cs);
      b_cs = a' (cs.b_cs);
      jlist_cs = map (fun i -> r(inc cs i )) cs.jlist_cs;
      attrib_cs = map (amap r) cs.attrib_cs;
    };;

let rotate_cs cs =
  let a' = fun i j -> cs.a_cs (inc cs i) (inc cs j) in
  let b' = fun i j -> cs.b_cs (inc cs i) (inc cs j) in
  let at' = map (inka cs.k_cs) cs.attrib_cs in
  {
  k_cs = cs.k_cs;
  d_cs = cs.d_cs;
  a_cs = a';
  b_cs = b';
  jlist_cs = map  (inc cs) cs.jlist_cs;
  attrib_cs = at';
  };;

let rec rotatek_cs k cs = 
  funpow k rotate_cs cs;;

let iso_strict_cs cs cs' = 
  let bk = cs.k_cs = cs'.k_cs in
  let bd = cs.d_cs = cs'.d_cs in
  let m r r' = ( uniq (map (fun (i,j) -> r i j = r' i j) (ks_cart cs)) = [true]) in
  let ba = m cs.a_cs cs'.a_cs in
  let bb = m cs.b_cs cs'.b_cs in
  let bj = (sortuniq cs.jlist_cs = sortuniq cs'.jlist_cs) in
  let bt = (sortuniq cs.attrib_cs = sortuniq cs'.attrib_cs) in
    bk && bd && ba && bb && bj && bt;;

let proper_iso_cs cs cs' = 
  Lib.exists (fun i -> iso_strict_cs (rotatek_cs i cs) cs') (ks_cs cs);;

let iso_cs cs cs' = 
  (cs.k_cs = cs'.k_cs) && 
 (  proper_iso_cs cs cs' or proper_iso_cs (reverse_cs cs) cs');;

let is_stable cs =
  let f (i,j) = 
    (i = j) or ((2.0 <= cs.a_cs i j) && (cs.a_cs i j <= cstab)) in
  let ks =  0 -- (cs.k_cs - 1) in
  let rl = cart ks ks in
  let bm = (uniq (map f rl) = [true]) in
  let bs = (uniq (map (fun i -> ((=) zero) (cs.a_cs i i)) ks) = [true]) in
  let g i = (cs.b_cs i (inc cs i) <= cstab) in
  let bs' = (uniq (map g ks) = [true]) in
  let fj i = not(mem i cs.jlist_cs) or 
    (sqrt8 = cs.a_cs i (inc cs i) && cs.b_cs i (inc cs i) = cstab) in
  let bj = (uniq (map fj ks) = [true]) in
    bm && bs && bs' && bj;;

(*
****************************************
FUNCTION BUILDERS
****************************************
*)

let cs_adj adj diag k i j = 
  if (i<0) or (j<0) or (i>=k) or (j>=k) then failwith "out of range"
  else if (i=j) then zero
  else if (j = ink k i) or (i = ink k j) then adj
  else diag;;

let a_pro pro adj diag k i j = 
  if (i<0) or (j<0) or (i>k) or (j>k) then failwith "out of range"
  else if (i=j) then zero
  else if (i=0 && j=1) or (j=0 && i=1) then pro
  else if (j = ink k i) or (i = ink k j) then adj
  else diag ;;

let psort (i,j) = (min i j),(max i j);;

let funlist data d i j = 
  if (i=j) then zero
  else assocd (psort (i,j)) data d;;

let override a (p,q,d) i j = 
  if (p,q) = psort (i,j) then d else a i j;;

let overrides a data i j = 
  funlist data (a i j) i j;;

(*
****************************************
TABLES OF CONSTRAINT SYSTEMS
****************************************
*)

let hex_std_cs = {
  k_cs = 6;
  d_cs = tame_table_d0 6;
  a_cs = cs_adj two twoh0 6;
  b_cs = cs_adj twoh0 six 6;
  jlist_cs = [];
  attrib_cs = [];
};;

let pent_std_cs = {
  k_cs = 5;
  d_cs = tame_table_d0 5;
  a_cs = cs_adj two twoh0 5;
  b_cs = cs_adj twoh0 six 5;
  jlist_cs = [];
  attrib_cs = [];
};;

let quad_std_cs = {
  k_cs = 4;
  d_cs = tame_table_d0 4;
  a_cs = cs_adj two twoh0 4;
  b_cs = cs_adj twoh0 six 4;
  jlist_cs = [];
  attrib_cs = [];
};;

let tri_std_cs = {
  k_cs = 3;
  d_cs = tame_table_d0 3;
  a_cs = cs_adj two twoh0 3;
  b_cs = cs_adj twoh0 six 3;
  jlist_cs = [];
  attrib_cs = [];
};;

let pent_diag_cs = {
  k_cs = 5;
  d_cs = 0.616;
  a_cs = cs_adj two sqrt8 5;
  b_cs = cs_adj twoh0 six 5;
  jlist_cs = [];
  attrib_cs = [];
};;

let quad_diag_cs = {
  k_cs = 4;
  d_cs = 0.467;
  a_cs = cs_adj two sqrt8 4;
  b_cs = cs_adj twoh0 six 4;
  jlist_cs = [];
  attrib_cs = [];
};;

let pent_pro_cs = 
{
  k_cs = 5;
  d_cs = 0.616;
  a_cs = a_pro twoh0 two twoh0 5;
  b_cs = a_pro sqrt8 twoh0 six 5;
  jlist_cs = [];
  attrib_cs = [];
};;

let quad_pro_cs = 
{
  k_cs = 4;
  d_cs = 0.477;
  a_cs = a_pro twoh0 two twoh0 4;
  b_cs = a_pro sqrt8 twoh0 six 4;
  jlist_cs = [];
  attrib_cs = [];
};;

let ur_cs = [
  hex_std_cs;
  pent_std_cs;
  quad_std_cs;
  tri_std_cs;
  pent_diag_cs;
  quad_diag_cs;
  pent_pro_cs;
  quad_pro_cs;
];;

(* now for the terminal cases done by interval computer calculation *)

let terminal_hex =
{
  k_cs = 6;
  d_cs = tame_table_d0 6;
  a_cs = cs_adj two cstab 6;
  b_cs = cs_adj two six 6;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_pent = 
{
  k_cs = 5;
  d_cs = 0.616;
  a_cs = cs_adj two cstab 5;
  b_cs = cs_adj two six 5;
  jlist_cs = [];
  attrib_cs = [];  
};;

(* two cases for the 0.467 bound: all top edges 2 or both diags 3 *)

let terminal_adhoc_quad_9563139965A = 
{
  k_cs = 4;
  d_cs = 0.467;
  a_cs = cs_adj two three 4;
  b_cs = cs_adj two six 4;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_adhoc_quad_9563139965B = 
{
  k_cs = 4;
  d_cs = 0.467;
  a_cs = cs_adj two three 4;
  b_cs = cs_adj twoh0 three 4;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_adhoc_quad_4680581274 = 
{
  k_cs = 4;
  d_cs = 0.616 -. 0.11;  (* was 0.696 in interval code *)
  a_cs = funlist [(0,1),cstab ; (0,2),cstab ; (1,3),cstab ] two;
  b_cs = funlist [(0,1),cstab ; (0,2),six ; (1,3),six ] two;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_adhoc_quad_7697147739 = 
{
  k_cs = 4;
  d_cs = 0.616 -. 0.11;  (* was 0.696 in interval code *)
  a_cs = funlist [(0,1),sqrt8 ; (0,2),cstab ; (1,3),cstab ] two;
  b_cs = funlist [(0,1),sqrt8 ; (0,2),six ; (1,3),six ] two;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_tri_3456082115 = 
  {
    k_cs = 3;
    d_cs = 0.5518 /. 2.0;
    a_cs = funlist [(0,1), cstab; (0,2),twoh0; (1,2),two] two;
    b_cs = funlist [(0,1), 3.22; (0,2),twoh0; (1,2),two] two;
    jlist_cs = [];
    attrib_cs = [];
  };;

let terminal_tri_7720405539 = 
{
  k_cs = 3;
  d_cs = 0.5518 /. 2.0 -. 0.2;
  a_cs = funlist [(0,1),cstab; (0,2),twoh0; (1,2),two] two;
  b_cs = funlist [(0,1),3.41; (0,2),twoh0; (1,2),two] two;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_tri_2739661360 = 
{
  k_cs = 3;
  d_cs = 0.5518 /. 2.0 +. 0.2;
  a_cs = funlist [(0,1),cstab; (0,2),cstab; (1,2),two] two;
  b_cs = funlist [(0,1),3.41; (0,2),cstab; (1,2),two] two;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_tri_9269152105 = 
{
  k_cs = 3;
  d_cs = 0.5518 /. 2.0 ;
  a_cs = funlist [(0,1),3.41; (0,2),cstab; (1,2),two] two;
  b_cs = funlist [(0,1),3.62; (0,2),cstab; (1,2),two] two;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_tri_4922521904 = 
{
  k_cs = 3;
  d_cs = 0.5518 /. 2.0 ;
  a_cs = funlist [(0,1),cstab; (0,2),twoh0; (1,2),two] two;
  b_cs = funlist [(0,1),3.339; (0,2),twoh0; (1,2),two] two;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_quad_1637868761 = 
{
  k_cs = 4;
  d_cs = 0.5518;
  a_cs = funlist [(0,1),two; (1,2), cstab; 
		  (2,3),twoh0; (0,3),two; (0,2),3.41; (1,3),cstab] two;
  b_cs = funlist [(0,1),two; (1,2), cstab;
		  (2,3),twoh0; (0,3),two; (0,2),3.634; (1,3),six] two;
  jlist_cs = [];
  attrib_cs = [];
};;

let ear_cs = 
{
  k_cs = 3;
  d_cs = 0.11;
  a_cs = funlist [(0,1),sqrt8] two;
  b_cs = funlist [(0,1),cstab] twoh0;
  jlist_cs = [0];
  attrib_cs = [];
};;

let terminal_ear_3603097872 = ear_cs;;


let terminal_tri_5405130650 = 
{
  k_cs = 3;
  d_cs =  0.477 -.  0.11;
  a_cs = funlist [(0,1),sqrt8;(0,2),twoh0;(1,2),two] two;
  b_cs = funlist [(0,1),cstab;(0,2),sqrt8;(1,2),twoh0] twoh0;
  jlist_cs = [0];
  attrib_cs = [];
};;

let terminal_tri_5766053833 = 
{
  k_cs = 3;
  d_cs =  0.696 -. 2.0 *. 0.11; 
  a_cs = funlist [(0,1),sqrt8;(1,2),sqrt8] two;
  b_cs = funlist [(0,1),cstab;(1,2),cstab] two;
  jlist_cs = [0;1];
  attrib_cs = [];
};;

let terminal_tri_5026777310 = 
{
  k_cs = 3;
  d_cs =  0.6548 -. 2.0 *. 0.11; 
  a_cs = funlist [(0,1),sqrt8;(1,2),sqrt8] two;
  b_cs = funlist [(0,1),cstab;(1,2),cstab] twoh0;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_tri_7881254908 = 
{
  k_cs = 3;
  d_cs =  0.696 -. 2.0 *. 0.11; 
  a_cs = funlist [(0,1),sqrt8;(1,2),sqrt8] twoh0;
  b_cs = funlist [(0,1),cstab;(1,2),cstab] twoh0;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_OMKYNLT_2_1  = (* 1107929058 *)
{
  k_cs = 3;
  d_cs =  tame_table_d 2 1;
  a_cs = funlist [(0,1),twoh0] two;
  b_cs = funlist [(0,1),twoh0] two;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_7645170609 = 
{
  k_cs = 3;
  d_cs =  tame_table_d 2 1;
  a_cs = funlist [(0,1),sqrt8] two;
  b_cs = funlist [(0,1),sqrt8] two;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_OMKYNLT_1_2  = (* 1532755966 *)
{
  k_cs = 3;
  d_cs =  tame_table_d 1 2;
  a_cs = funlist [(0,1),two] twoh0;
  b_cs = funlist [(0,1),two] twoh0;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_7097350062 = 
{
  k_cs = 3;
  d_cs =  tame_table_d 1 2 +. (tame_table_d 2 1 -. 0.11);
  a_cs = funlist [(0,1),twoh0;(0,2),sqrt8] two;
  b_cs = funlist [(0,1),twoh0;(0,2),sqrt8] two;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_2900061606 = 
{
  k_cs = 3;
  d_cs =  tame_table_d 1 2 +. (tame_table_d 2 1 -. 0.11);
  a_cs = funlist [(0,1),twoh0;(0,2),cstab] two;
  b_cs = funlist [(0,1),twoh0;(0,2),cstab] two;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_2200527225 = 
{
  k_cs = 3;
  d_cs =  tame_table_d 1 2 +. 2.0*. (tame_table_d 2 1 -. 0.11);
  a_cs = funlist [(0,1),two;] sqrt8;
  b_cs = funlist [(0,1),two;] sqrt8;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_3106201101 = 
{
  k_cs = 3;
  d_cs =  tame_table_d 1 2 +. 2.0*. (tame_table_d 2 1 -. 0.11);
  a_cs = funlist [(0,1),two;(0,2),cstab] sqrt8;
  b_cs = funlist [(0,1),two;(0,2),cstab] sqrt8;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_9816718044 = 
{
  k_cs = 3;
  d_cs =  tame_table_d 1 2 +. 2.0*. (tame_table_d 2 1 -. 0.11);
  a_cs = funlist [(0,1),two] cstab;
  b_cs = funlist [(0,1),two] cstab;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_1080462150 = 
{
  k_cs = 3;
  d_cs =  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11);
  a_cs = funlist [] twoh0;
  b_cs = funlist [] twoh0;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_4143829594 =
{
  k_cs = 3;
  d_cs =  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11);
  a_cs = funlist [(0,1),cstab] twoh0;
  b_cs = funlist [(0,1),cstab] twoh0;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_7459553847 =
{
  k_cs = 3;
  d_cs =  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11);
  a_cs = funlist [(0,1),twoh0] cstab;
  b_cs = funlist [(0,1),twoh0] cstab;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_4528012043 =
{
  k_cs = 3;
  d_cs =  tame_table_d 0 3 +. 3.0 *.(tame_table_d 2 1 -. 0.11);
  a_cs = funlist [] cstab;
  b_cs = funlist [] cstab;
  jlist_cs = [];
  attrib_cs = [];
};;

let terminal_std_tri_OMKYNLT_3336871894 = 
{
  k_cs = 3;
  d_cs = zero;
  a_cs = funlist [] two;
  b_cs = funlist [] two;
  jlist_cs = [];
  attrib_cs = [];
};;


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

let is_ear cs = 
  iso_cs ear_cs cs;;




(*
let sigma_cs cs = 
  if is_ear cs then 1.0 else -1.0;;

let slice_filter_attrib k k' p a =
  let r i = (i + k - p) mod k in
  let s i' = (i' + p) mod k in
    match a with
      | Cs_straight i -> 
	  let r' = r i in
	  if (r'= 0 or k' <= r' +1) then None else Some (Cs_straight r')
      | Cs_lo i -> Some(Cs_lo (r'

*)

(*
****************************************
TRANSFORMATIONS
****************************************
*)


let transfer_to = 
  let b1 cs cs' = (cs.k_cs =  cs'.k_cs) in
  let b2 cs cs' = (cs.d_cs <= cs'.d_cs) in
  let c3 cs cs' (i,j) = 
    cs.a_cs i j >= cs'.a_cs i j  && cs.b_cs i j <= cs'.b_cs i j  in
  let b3 cs cs' =
      (uniq (map (c3 cs cs') (ks_cart cs)) = [true]) in
  let b4 cs cs' = 
    if is_ear cs then iso_cs cs cs'
    else Lib.subset cs'.jlist_cs cs.jlist_cs in
  let b5 cs cs' = 
    Lib.subset (sortuniq cs'.attrib_cs) (sortuniq  cs.attrib_cs) in
    fun cs cs' -> 
      b1 cs cs' && b2 cs cs' && b3 cs cs' && b4 cs cs' && b5 cs cs';;

let proper_transfer_cs cs cs' = 
  Lib.exists (fun i -> transfer_to (rotatek_cs i cs) cs') (ks_cs cs);;

let iso_transfer_cs cs cs' = 
  (cs.k_cs = cs'.k_cs) && 
 (  proper_transfer_cs cs cs' or proper_transfer_cs (reverse_cs cs) cs');;

let divide_cs p q c cs =
  let _ = (0 <= p && p< cs.k_cs) or failwith "p out of range divide_cs" in
  let _ = (0 <= q && q< cs.k_cs) or failwith "q out of range divide_cs" in
  let (p,q) = psort(p,q) in
  let a = cs.a_cs p q in
  let b = cs.b_cs p q in
    if (c <= a  or b <= c) then [cs] 
    else
      let cs1 = {
	k_cs = cs.k_cs;
	a_cs = cs.a_cs;
	d_cs = cs.d_cs;
	b_cs = override cs.b_cs (p,q,c);
	jlist_cs = cs.jlist_cs;
	attrib_cs = cs.attrib_cs;
      } in
      let cs2 = {
	k_cs = cs.k_cs;
	b_cs = cs.b_cs;
	d_cs = cs.d_cs;
	a_cs = override cs.a_cs (p,q,c);
	jlist_cs = cs.jlist_cs;
	attrib_cs = cs.attrib_cs;
      } in
	[cs1;cs2];;


let deform_ODXLSTC_cs p cs = 
  let p0 = dec cs p in
  let p1 = p in
  let p2 = inc cs p in
  if (mem (Cs_lo p) cs.attrib_cs or
      (cs.a_cs p1 p2 = cs.b_cs p1 p2) or
      (cs.a_cs p1 p0 = cs.b_cs p1 p0) or 
      (mem p1 cs.jlist_cs) or 
      (mem p0 cs.jlist_cs) or
      not (is_stable cs) or
     not (mem Cs_interior_crit cs.attrib_cs))
  then [cs]
  else
    let cs1 = {
      k_cs = cs.k_cs;
      a_cs = cs.a_cs;
      b_cs = cs.b_cs;
      d_cs = cs.d_cs;
      jlist_cs = cs.jlist_cs;
      attrib_cs = (Cs_lo p)::cs.attrib_cs;
    } in
    let cs2 = {
      k_cs = cs.k_cs;
      a_cs = cs.a_cs;
      b_cs = override cs.b_cs (p1,p2,cs.a_cs p1 p2);
      d_cs = cs.d_cs;
      jlist_cs = cs.jlist_cs;
      attrib_cs = cs.attrib_cs;
    } in
    let cs3 = {
      k_cs = cs.k_cs;
      a_cs = cs.a_cs;
      b_cs = override cs.b_cs (p1,p0,cs.a_cs p1 p0);
      d_cs = cs.d_cs;
      jlist_cs = cs.jlist_cs;
      attrib_cs = cs.attrib_cs;
    } in
      [cs1;cs2;cs3];;

let deform_IMJXPHR_cs p cs = 
  let p0 = dec cs p in
  let p1 = p in
  let p2 = inc cs p in
  if (mem (Cs_lo p) cs.attrib_cs or
      ((cs.a_cs p1 p2 = cs.b_cs p1 p2) and
      (cs.a_cs p1 p0 = cs.b_cs p1 p0)) or 
      (mem p1 cs.jlist_cs) or (mem p0 cs.jlist_cs) or
      not (is_stable cs) or
      not (mem (Cs_straight p) cs.attrib_cs)
  then [cs]
  else
    let cs1 = {
      k_cs = cs.k_cs;
      a_cs = cs.a_cs;
      b_cs = cs.b_cs;
      d_cs = cs.d_cs;
      jlist_cs = cs.jlist_cs;
      attrib_cs = (Cs_lo p)::cs.attrib_cs;
    } in
    let cs2 = {
      k_cs = cs.k_cs;
      a_cs = cs.a_cs;
      b_cs = overrides cs.b_cs [(p1,p2),cs.a_cs p1 p2;(p1,p0),cs.a_cs p1 p0];
      d_cs = cs.d_cs;
      jlist_cs = cs.jlist_cs;
      attrib_cs = cs.attrib_cs;
    } in
      [cs1;cs2];;
    

(*
let slice_dcs p q isj isear av bv dv cs = 
  let k = cs.k_cs in
  let p = p mod k in
  let q = q mod k in
  let q' = if (q<p) then q+k else q in
  let k' = 1+q'-p in
  let _ = (k' >2) or failwith "slice_dcs underflow" in
  let _ = (k'  <  k) or failwith "slice_dcs overflow" in
  let _ = (av <= cs.a_cs && cs.b_cs <= bv) or failwith "slice range" in
  let _ = not(isear) or (av=sqrt8 && bv=cstab) or failwith "slice ear" in
  let r i = (i + k - p) mod k in
  let s i' = (i' + p) mod k in

  let af a d i' j' =      
    let i = s i' in
    let j = s j' in
      if (i'=0 && j'+1=k') or (j'=0 && i'+1=k') then d
      else if (i' < k') && (j' < k') then a i j 
      else failwith "out of range a" in
  let jlist = filter (fun i -> i+1 < k') (map r cs.jlist_cs) in
  let jlist' = if isear then (k'-1) :: jlist  else jlist in
   {
    k_cs = q'-p;
    d_cs = dv;
    a_cs = af cs.a_cs av;
    b_cs = af cs.a_cs bv;
    jlist_cs =  jlist';
    attrib_cs = [];
  } ;;
*)

type vef = {
  vl : int;
  ht : int -> float;
  az : int -> float;
  ed : int -> int -> float;
};;

(*
let dsv cs v = 
  let f i = (cstab - v.ed i (ink v.vl i)) in
  let u = end_itlist (+.) (map f 
  cs.d_cs + 0.1 * 
    let 
*)


