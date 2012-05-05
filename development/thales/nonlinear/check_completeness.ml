(* 
Thomas Hales,
May 5, 2012
Check completeness (informally) 
of case anaysis in proof of Kepler conjecture, Main Estimate.
*)


(* Start with hexagon case. tameTableD[6,0] = 0.712. *)

#directory "/Users/thomashales/Desktop/googlecode/hol_light";;
#use "hol.ml";;

type constraint_system = 
{
  k_cs : int;
  d_cs : float;
  a_cs : int->int ->float;
    b_cs: int->int->float;
    jlist_cs : int list;
};;

let ink i k = (i+1) mod k;;

let inc cs i = ink i cs.k_cs;;

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
let two = 2.0;;
let twoh0 = 2.52;;
let fourh0 = 2.0 *. twoh0;;

let eps_close a b = Pervasives.abs_float (a -. b) < 10.0**(-8.0);;

let is_stable cs =
  let f (i,j) = 
    (i = j) or ((2.0 <= cs.a_cs i j) && (cs.a_cs i j <= cstab)) in
  let ks =  0 -- (cs.k_cs - 1) in
  let rl = cart ks ks in
  let bm = (nub (map f rl) = [true]) in
  let bs = (nub (map (fun i -> eps_close(0.0) (cs.a_cs i i)) ks) = [true]) in
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

fun cs i j -> if (i < 0) or (j < 0) or (i > 6) or  (j > 6) then failwith "out of range"
    else if (i = j) then 0.0
    else if (j = inc cs i) or (i = inc cs j) then two else twoh0;;

let hex_standard_cs = {
  k_cs = 6;
  d_cs = 0.712;
  a_cs = (fun i j -> if (i < 0) or (j < 0) or (i > 6) or  (j > 6) then failwith "out of range"
    else if (i = j) then 0.0
    else if (j = ink i 6) or (i = ink j 6) then two else twoh0);
  b_cs = (fun i j -> if (i < 0) or (j < 0) or (i > 6) or  (j > 6) then failwith "out of range"
    else if (i = j) then 0.0
    else if (j = ink i 6) or (i = ink j 6) then twoh0 else fourh0);
  jlist_cs = [];
};;

is_cs hex_standard_cs;;
is_stable hex_standard_cs;;

let ear_cs = {
  
};;

type vef = {
  vl : int;
  ht : int -> float;
  az : int -> float;
  ed : int -> int -> float;
};;
