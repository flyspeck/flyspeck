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
*)


(* Start with hexagon case. tameTableD[6,0] = 0.712. *)

#directory "/Users/thomashales/Desktop/googlecode/hol_light";;
#use "hol.ml";;

(*
look only at global minumum points for tau*(s,v) (for s fixed)
and such that tau*(s,v)<=0.
Let index(v) = the number of edges st |vi-vj|=a(i,j). 
and such that index(v) is minimized among global minimum points in Bs.
Call this set IB(s) (index-global-min).
*)



type attrib_cs =
    Cs_straight of int
  | Cs_lo  of int
  | Cs_hi of int
(*  | Cs_min of int*int
  | Cs_max of int*int *)
  | Cs_interior_crit of int*int;;

let amap f a = match a with
      | Cs_straight i -> Cs_straight (f i)
      | Cs_lo i -> Cs_lo (f i)
      | Cs_hi i -> Cs_hi (f i)
(*      | Cs_min (i,j) -> Cs_min (f i , f j)
      | Cs_max (i,j) -> Cs_max (f i, f j) *)
      | Cs_interior_crit (i,j) -> Cs_interior_crit (f i, f j);;

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

let inc cs i = ink cs.k_cs i;;

let inka k a = 
    amap (ink k) a;;

let in_j cs (i,j) = 
  ((j = inc cs i) && (mem i cs.jlist_cs)) or
   ( (i = inc cs j) &&( mem j cs.jlist_cs));;

let rec nub = function (* from lpproc.ml *)
  | [] -> []
  | x::xs -> x::filter ((<>) x) (nub xs);;

let rec cart a b = 
  match a with
    | [] -> []
    | a::rest -> (map (fun x -> (a,x)) b) @ cart rest b;;

let is_cs cs = 
  let f (i,j) = 
    (cs.a_cs i j = cs.a_cs j i) &&
      (cs.b_cs i j = cs.b_cs j i) &&
      (cs.a_cs i j <= cs.b_cs i j) in
  let ks = 0 -- (cs.k_cs - 1) in
  let rl = cart ks ks in
  let bm = (nub (map f rl) = [true]) in 
  let bs = (cs.k_cs <= 6) && (cs.k_cs >= 3) in
  let bj = List.length cs.jlist_cs + cs.k_cs <= 6 in
  let bj' = List.length (nub cs.jlist_cs) = List.length cs.jlist_cs in
    bm && bs && bj && bj';;  

let cstab = 3.01;;
let sqrt8 = Pervasives.sqrt(8.0);;
let zero = 0.0;;
let two = 2.0;;
let twoh0 = 2.52;;
let six = 6.0;;  (* 6.0 > 4 * h0, upper bound on diags in BB *)
let target = 1.541;;

let tame_table_d i = 
  if (i <= 3) then zero
  else if (i=4) then 0.206 
  else if (i=5) then 0.4819
  else if (i=6) then 0.712
  else target;;

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

let ks_cs cs = (0-- (cs.k_cs -1));;

let ks_cart cs = let ks = ks_cs cs in cart ks ks;;

let iso_strict_cs cs cs' = 
  let bk = cs.k_cs = cs'.k_cs in
  let bd = cs.d_cs = cs'.d_cs in
  let m r r' = ( nub (map (fun (i,j) -> r i j = r' i j) (ks_cart cs)) = [true]) in
  let ba = m cs.a_cs cs'.a_cs in
  let bb = m cs.b_cs cs'.b_cs in
  let bj = (nub (Lib.sort (<) cs.jlist_cs) = nub (Lib.sort (<) cs'.jlist_cs)) in
  let bt = (nub (Lib.sort (<) cs.attrib_cs) = nub(Lib.sort (<) cs'.attrib_cs)) in
    bk && bd && ba && bb && bj && bt;;

let proper_iso_cs cs cs' = 
  Lib.exists (fun i -> iso_strict_cs (rotatek_cs i cs) cs') (ks_cs cs);;

let iso_cs cs cs' = 
  (cs.k_cs = cs'.k_cs) && 
 (  proper_iso_cs cs cs' or proper_iso_cs (reverse_cs cs) cs');;

(*
let eps_close a b = Pervasives.abs_float (a -. b) < 10.0**(-8.0);;
*)

let is_stable cs =
  let f (i,j) = 
    (i = j) or ((2.0 <= cs.a_cs i j) && (cs.a_cs i j <= cstab)) in
  let ks =  0 -- (cs.k_cs - 1) in
  let rl = cart ks ks in
  let bm = (nub (map f rl) = [true]) in
  let bs = (nub (map (fun i -> ((=) zero) (cs.a_cs i i)) ks) = [true]) in
  let g i = (cs.b_cs i (inc cs i) <= cstab) in
  let bs' = (nub (map g ks) = [true]) in
  let fj i = not(mem i cs.jlist_cs) or 
    (sqrt8 = cs.a_cs i (inc cs i) && cs.b_cs i (inc cs i) = cstab) in
  let bj = (nub (map fj ks) = [true]) in
    bm && bs && bs' && bj;;

let csk cs = cs.k_cs;;
let csa cs i j = cs.a_cs i j;;
let csb cs i j = cs.b_cs i j;;
let csd cs  = cs.d_cs;;

(*
fun cs i j -> if (i < 0) or (j < 0) or (i > 6) or  (j > 6) then failwith "out of range"
    else if (i = j) then 0.0
    else if (j = inc cs i) or (i = inc cs j) then two else twoh0;;
*)

let cs_adj adj diag k i j = 
  if (i<0) or (j<0) or (i>k) or (j>k) then failwith "out of range"
  else if (i=j) then zero
  else if (j = ink k i) or (i = ink k j) then adj
  else diag;;

let hex_std_cs = {
  k_cs = 6;
  d_cs = tame_table_d 6;
  a_cs = cs_adj two twoh0 6;
  b_cs = cs_adj twoh0 six 6;
  jlist_cs = [];
  attrib_cs = [];
};;

is_cs hex_std_cs;;
is_stable hex_std_cs;;

let pent_std_cs = {
  k_cs = 5;
  d_cs = tame_table_d 5;
  a_cs = cs_adj two twoh0 5;
  b_cs = cs_adj twoh0 six 5;
  jlist_cs = [];
  attrib_cs = [];
};;

let quad_std_cs = {
  k_cs = 4;
  d_cs = tame_table_d 4;
  a_cs = cs_adj two twoh0 4;
  b_cs = cs_adj twoh0 six 4;
  jlist_cs = [];
  attrib_cs = [];
};;

let tri_std_cs = {
  k_cs = 3;
  d_cs = tame_table_d 3;
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

  let a_pro pro adj diag k i j = 
    if (i<0) or (j<0) or (i>k) or (j>k) then failwith "out of range"
    else if (i=j) then zero
    else if (i=0 && j=1) or (j=0 && i=1) then pro
    else if (j = ink k i) or (i = ink k j) then adj
    else diag ;;

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

let ear_cs = 
  let a i j = 
    if (i=j) then zero
    else if (i = 0) or (j=0) then sqrt8
    else two  in
  let b i j = 
    if (i=j) then zero
    else if (i = 0) or (j=0) then cstab
    else twoh0 in
      {
  k_cs = 3;
  d_cs = 0.11;
  a_cs = a;
  b_cs = b;
  jlist_cs = [0];
  attrib_cs = [];
};;

let is_ear cs = 
  iso_cs ear_cs cs;;

is_cs ear_cs;;
is_stable ear_cs;;
is_ear (reverse_cs ear_cs);;

let sigma_cs cs = 
  if is_ear cs then 1.0 else -1.0;;

(*
let slice_filter_attrib k k' p a =
  let r i = (i + k - p) mod k in
  let s i' = (i' + p) mod k in
    match a with
      | Cs_straight i -> 
	  let r' = r i in
	  if (r'= 0 or k' <= r' +1) then None else Some (Cs_straight r')
      | Cs_lo i -> Some(Cs_lo (r'


type attrib_cs =
    Cs_straight of int
  | Cs_lo  of int
  | Cs_hi of int
  | Cs_interior_crit  of int*int;;

(*  | Cs_min of int*int
  | Cs_max of int*int *)
*)

let sortattrib cs = nub (Lib.sort (<) cs.attrib_cs);;

let transfer_to = 
  let b1 cs cs' = (cs.k_cs =  cs'.k_cs) in
  let b2 cs cs' = (cs.d_cs <= cs'.d_cs) in
  let c3 cs cs' (i,j) = 
    cs.a_cs i j >= cs'.a_cs i j  && cs.b_cs i j <= cs'.b_cs i j  in
  let b3 cs cs' =
      (nub (map (c3 cs cs') (ks_cart cs)) = [true]) in
  let b4 cs cs' = 
    if is_ear cs then iso_cs cs cs'
    else Lib.subset cs'.jlist_cs cs.jlist_cs in
  let b5 cs cs' = 
    Lib.subset (sortattrib cs') (sortattrib cs) in
    fun cs cs' -> 
      b1 cs cs' && b2 cs cs' && b3 cs cs' && b4 cs cs' && b5 cs cs';;

let divide_cs p q c cs =
  let _ = (0 <= p && p< cs.k_cs) or failwith "p out of range divide_cs" in
  let _ = (0 <= q && q< cs.k_cs) or failwith "q out of range divide_cs" in
  let a = cs.a_cs p q in
  let b = cs.b_cs p q in
  let _ = (a <= c && c <= b) or failwith "c out of range divide_cs" in
  let cs1 = {
    k_cs = cs.k_cs;
    a_cs = cs.a_cs;
    d_cs = cs.d_cs;
    b_cs = (fun i j -> 
	      if (((i,j)=(p,q)) or ((i,j)=(p,q))) then c else cs.b_cs i j);
    jlist_cs = cs.jlist_cs;
    attrib_cs = filter (fun u -> not (u = Cs_interior_crit (p, q)) && not (u= Cs_interior_crit (q ,p))) cs.attrib_cs;
  } in
  let cs2 = {
    k_cs = cs.k_cs;
    b_cs = cs.b_cs;
    d_cs = cs.d_cs;
    a_cs = (fun i j -> 
	      if (((i,j)=(p,q)) or ((i,j)=(p,q))) then c else cs.a_cs i j);
    jlist_cs = cs.jlist_cs;
    attrib_cs = filter (fun u -> not (u = Cs_interior_crit (p, q)) && not (u= Cs_interior_crit (q ,p))) cs.attrib_cs;
  } in
    (cs1,cs2);;

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


