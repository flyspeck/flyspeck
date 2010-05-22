(*
Created Nov 26, 2009
THALES
Compute irreducible cyclic fans.
*)

(*
Needs.
k nodes, k edges {i,i+1},
cyclic map on both
Each node is 2, 2h0 or free.
Each node is flat or not flat.

Each edge is in G or not,
Each edge is 2, 2h0, or free.

*)
open List;;

(* from lpproc.ml *)
let upto = 
  let rec rangeA a i j  = if (i >= j) then a
   else rangeA ((j-1)::a) i (j-1)  in
  rangeA [] 0;;


(* minimal fan definition *)

type node_t = N2 | N2h0 | Nfree;;
type edge_t = E2 | E2h0 | Gset;;


type minimal_fan =  {
  node : node_t list;
  nodeflats : bool list;
  edge : edge_t list;
};;

let mk_minimal_fan nhts nflts e =
   {
   node = nhts;
   nodeflats = nflts;
   edge = e;
   };;


(* generating minimal_fan *)

let node_of_int i = if (i=0) then N2 else if (i=1) then N2h0 else Nfree;;
let edge_of_int i = if (i=0) then E2 else if (i=1) then E2h0 else Gset;;
let bool_of_int i = if (i=0) then false else true;;

let base modulus len k =
  let rec baselist modulus len k acc = 
    if len <= 0 then acc else
    if (k=0) then baselist modulus (len-1) 0 (0::acc)
    else 
      baselist modulus (len - 1) (k/modulus) ((k mod modulus) :: acc) in
  baselist modulus len k [];;

let rec pow base exp =
   if exp = 0 then 1 else base*(pow base (exp-1));;

let mk_x len (a,b,c) (r,s,t) =
  let (n,nf,e) = (base a len r, base b len s, base c len t) in
  mk_minimal_fan 
     (map node_of_int n)
     (map bool_of_int nf)
     (map edge_of_int e);;

(* reading data from a record *)

let kn mf = length (mf.node);;
let sn mf = List.length (filter ((=) Gset) mf.edge);;
let rn mf = kn mf - sn mf;;

let posmod i m = 
  let j = i mod m in
  if (j<0) then j+m else j;;
  
let part xs i = nth xs (posmod i (length xs));;

let number mf = upto(length mf.edge);;

let g_edge mf i = (part mf.edge i = Gset);;
(* let nong_edge mf i = not(g_edge mf i);; *)
let gminimal_edge mf i = not(part mf.edge i = E2h0);;

let flat_node mf i = part mf.nodeflats i;;
let nonflat_node mf i = not(flat_node mf i);;
let bound_node mf i = not(part mf.node i = Nfree);;

(* irreducibility *)

(* extreme_edge is built into construction of edge types *)

let card mf = (sn mf <= 3) && (3 <= sn mf + rn mf) && (rn mf + 2 * sn mf <= 6);;

let extreme_edge mf = true;;

let flat_exists mf = 
  let has i = (kn mf <= 4) or
       flat_node mf i or flat_node mf (i+1) or flat_node mf (i+2) or flat_node mf (i+3) in
  for_all has (number mf);;

let no_triple_flat mf = 
   let triple_flat i = flat_node mf i && flat_node mf (i+1) && flat_node mf (i+2) in
   not (exists triple_flat (number mf));;

let balance mf = 
   let es = mf.edge in
   let has_balance i = (part es i = part es (i+1)) or (part es i = Gset) or (part es (i+1) = Gset) in
   for_all has_balance (number mf);;

let g_flat mf = 
   let gg = g_edge mf in
  let nf = nonflat_node mf in
  let has_gflat i = nf i or nf (i+1) or not(gg (i-1) or gg i or gg(i+1) ) in
   for_all has_gflat (number mf);;

let flat_middle mf =
  let nf = nonflat_node mf in
  let has i = nf i or nf (i+1) or (part mf.edge i = E2 ) in
   for_all has (number mf);;

let minimal_node mf = 
  let has i = (part mf.node i = N2) or (gminimal_edge mf i) or (gminimal_edge mf (i-1)) in
  for_all has (number mf);;

let minimal_node_flat mf = 
  let has i = (nonflat_node mf i) or (part mf.node i = N2) or (gminimal_edge mf i && gminimal_edge mf (i-1)) in
  for_all has (number mf);;

let flat_extremal mf = 
  let has i = nonflat_node mf i or nonflat_node mf (i+1) or bound_node mf i or bound_node mf (i+1) in
  for_all has (number mf);;

let extremal_node mf = 
  let has i = flat_node mf i or flat_node mf (i+1) or flat_node mf (i+2) or bound_node mf (i+1) in
  for_all has (number mf);; 

let flat_extremal_node mf = 
   let has i = flat_node mf i or nonflat_node mf (i+1) or flat_node mf (i+2) or flat_node mf (i+3) or bound_node mf (i+1) or bound_node mf (i+2) in
  for_all has (number mf);;

let flat_extremal_node_sym mf = 
   let has i = flat_node mf i or flat_node mf (i+1) or nonflat_node mf (i+2) or flat_node mf (i+3) or bound_node mf (i+1) or bound_node mf (i+2) in
  for_all has (number mf);;

let flat_count mf = 
   length (filter not mf.nodeflats) > 2;;

let irreducible = 
  fold_right (fun r s m -> r m && s m) 
 [card;extreme_edge;flat_exists;no_triple_flat;balance;g_flat;
  flat_middle;minimal_node;minimal_node_flat;flat_extremal;
  extremal_node;flat_extremal_node;flat_extremal_node_sym;
  flat_count] 
(fun t->true);;


(* symmetry reductions, add to the list of solutions only if it is shift-distinct from other solutions *)

let shift_one (x::xs) = xs @ [x];;

let shift a = { node = shift_one a.node; nodeflats = shift_one a.nodeflats; edge = shift_one a.edge };;

let rec shiftk k a =  if (k<=0) then a else shift (shiftk (k-1) a);;

let add_if_new a xs = 
   if (exists (fun i -> mem (shiftk i a) xs) (upto (kn a))) then xs else a::xs;;
let add_if_irred a xs = if (irreducible a ) then add_if_new a xs else xs;;
(* let add_if_irred a xs = if (irreducible a ) then a ::xs else xs;; *)

let rec mk_all mkfn (imin,jmin,kmin) (imax,jmax,kmax) (i, j, k) acc  = 
  let acc' = add_if_irred (mkfn (i, j, k)) acc in
  let mka = mk_all mkfn (imin,jmin,kmin) (imax,jmax,kmax) in
  if (k+1 < kmax) then mka (i,j,(k+1)) acc'
  else if (j+1 < jmax) then mka (i,(j+1),kmin) acc'
  else if (i+1 < imax) then mka ((i+1),jmin,kmin) acc'
  else acc';;

(* no flats *)
let a3 = mk_all (mk_x 3 (3,1,3)) (0,0,0) (pow 3 3,1,pow 3 3) (0,0,0) [];;
length a3;;

(* no flats *)
let a4nf = mk_all (mk_x 4 (3,1,3)) (0,0,0) (pow 3 4,1,pow 3 4) (0,0,0) [];;
length a4nf;;

(* exactly one flat *)
let a4f = mk_all (mk_x 4 (3,2,3)) (0,1,0) (pow 3 4,2,pow 3 4) (0,1,0) [];;
length a4f;;

(* no Gset *)
(*
let a5ng =mk_all (mk_x 5 (3,2,2)) (0,0,0) (pow 3 5,pow 2 5,pow 2 5) (0,0,0) [];;
length a5ng;;
*)

let a5 = mk_all (mk_x 5 (3,2,3)) (0,0,0) (pow 3 5,pow 2 5,pow 3 5) (0,0,0) [];;
length a5;;

(* no Gset *)
let a6 = mk_all (mk_x 6 (3,2,2)) (0,0,0) (pow 3 6,pow 2 6,pow 2 6) (0,0,0) [];;
length a6;;

(* degrees of freedom *)

let freedom a = (kn a) - 3 + length (filter ((=) Nfree) a.node) - length (filter (fun t->t) a.nodeflats);;
map freedom a4nf;;
